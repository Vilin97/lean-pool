/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Matrix.Order

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Foundational definitions for viscosity solutions

This file contains the ambient coordinate model, jets, quadratic models, and
abstract second-order expansion predicates used throughout the formalization.
-/

@[expose] public noncomputable section

open Filter
open Matrix
open scoped MatrixOrder

namespace ViscositySolns

/-- The ambient Euclidean coordinate space `R^n`, represented as functions on `Fin n`. -/
abbrev Point (n : Nat) : Type :=
  Fin n -> Real

theorem nhdsWithin_eq_of_subset_of_mem_nhdsWithin {α : Type*} [TopologicalSpace α]
    {K C : Set α} {x : α} (hKC : K ⊆ C) (hK : K ∈ nhdsWithin x C) :
    nhdsWithin x K = nhdsWithin x C := by
  have h := nhdsWithin_inter_of_mem (a := x) (s := K) (t := C) hK
  have hKC_eq : K ∩ C = K := Set.inter_eq_left.2 hKC
  simpa [hKC_eq] using h

theorem eventually_mem_nhdsWithin_of_mem_nhdsWithin_of_tendsto
    {α ι : Type*} [TopologicalSpace α] {K C : Set α} {x : α}
    {xᵢ : ι -> α} {l : Filter ι}
    (hK : K ∈ nhdsWithin x C) (hx : Tendsto xᵢ l (nhds x))
    (hmem : ∀ᶠ i in l, xᵢ i ∈ C) :
    ∀ᶠ i in l, K ∈ nhdsWithin (xᵢ i) C := by
  rw [mem_nhdsWithin] at hK
  rcases hK with ⟨U, hUopen, hxU, hUC⟩
  have hU : U ∈ nhds x := hUopen.mem_nhds hxU
  filter_upwards [hx hU, hmem] with i hxiU _hxiC
  rw [mem_nhdsWithin]
  exact ⟨U, hUopen, hxiU, hUC⟩

/-- Hessian matrices for scalar equations on `R^n`. -/
abbrev Hessian (n : Nat) : Type :=
  Matrix (Fin n) (Fin n) Real

/-- First and second derivative data used in the second-order semijets. -/
structure Jet (n : Nat) where
  /-- First derivative in coordinate form. -/
  gradient : Point n
  /-- Second derivative in coordinate matrix form. -/
  hessian : Hessian n

/-- A scalar fully nonlinear second-order operator `F(x, r, p, X)`. -/
abbrev Operator (n : Nat) : Type :=
  Point n -> Real -> Point n -> Hessian n -> Real

namespace Jet

variable {n : Nat}

/-- Jets are equivalent to their gradient/Hessian product data. -/
def equivProd (n : Nat) : Jet n ≃ Point n × Hessian n where
  toFun J := (J.gradient, J.hessian)
  invFun P := { gradient := P.1, hessian := P.2 }
  left_inv J := by cases J; rfl
  right_inv P := by cases P; rfl

/-- The product topology on jets, induced by their gradient and Hessian components. -/
instance instTopologicalSpace : TopologicalSpace (Jet n) :=
  TopologicalSpace.induced (fun J : Jet n => (J.gradient, J.hessian)) inferInstance

/-- The gradient projection from jets is continuous. -/
theorem continuous_gradient : Continuous fun J : Jet n => J.gradient := by
  have hdata : Continuous fun J : Jet n => (J.gradient, J.hessian) := continuous_induced_dom
  exact continuous_fst.comp hdata

/-- The Hessian projection from jets is continuous. -/
theorem continuous_hessian : Continuous fun J : Jet n => J.hessian := by
  have hdata : Continuous fun J : Jet n => (J.gradient, J.hessian) := continuous_induced_dom
  exact continuous_snd.comp hdata

/-- The zero jet has zero first- and second-order parts. -/
instance instZero : Zero (Jet n) := (equivProd n).zero

@[simp]
theorem zero_gradient : (0 : Jet n).gradient = 0 :=
  rfl

@[simp]
theorem zero_hessian : (0 : Jet n).hessian = 0 :=
  rfl

/-- Jets add componentwise. -/
instance instAdd : Add (Jet n) where
  add J K :=
    { gradient := J.gradient + K.gradient
      hessian := J.hessian + K.hessian }

/-- Jets form an additive commutative group under componentwise addition. -/
instance instAddCommGroup : AddCommGroup (Jet n) := (equivProd n).addCommGroup

@[simp]
theorem add_gradient (J K : Jet n) : (J + K).gradient = J.gradient + K.gradient :=
  rfl

@[simp]
theorem add_hessian (J K : Jet n) : (J + K).hessian = J.hessian + K.hessian :=
  rfl

@[simp]
theorem neg_gradient' (J : Jet n) : (-J).gradient = -J.gradient :=
  rfl

@[simp]
theorem neg_hessian' (J : Jet n) : (-J).hessian = -J.hessian :=
  rfl

@[simp]
theorem sub_gradient (J K : Jet n) : (J - K).gradient = J.gradient - K.gradient :=
  rfl

@[simp]
theorem sub_hessian (J K : Jet n) : (J - K).hessian = J.hessian - K.hessian :=
  rfl

/-- Scalar multiplication of jets is componentwise. -/
instance instSMul : SMul Real (Jet n) where
  smul a J :=
    { gradient := a • J.gradient
      hessian := a • J.hessian }

@[simp]
theorem smul_gradient (a : Real) (J : Jet n) : (a • J).gradient = a • J.gradient :=
  rfl

@[simp]
theorem smul_hessian (a : Real) (J : Jet n) : (a • J).hessian = a • J.hessian :=
  rfl

/-- Negating a jet negates both first- and second-order parts. -/
def neg (J : Jet n) : Jet n where
  gradient := -J.gradient
  hessian := -J.hessian

@[simp]
theorem neg_gradient (J : Jet n) : J.neg.gradient = -J.gradient :=
  rfl

@[simp]
theorem neg_hessian (J : Jet n) : J.neg.hessian = -J.hessian :=
  rfl

@[simp]
theorem neg_eq_neg (J : Jet n) : -J = J.neg :=
  rfl

end Jet

variable {n : Nat}

/--
The quadratic polynomial determined by a value, gradient, and Hessian at `x0`,
evaluated at `x`.
-/
def quadraticModel (x0 : Point n) (r : Real) (p : Point n) (X : Hessian n)
    (x : Point n) : Real :=
  let dx : Point n := x - x0
  r + dotProduct p dx + (1 / 2 : Real) * dotProduct (Matrix.mulVec X dx) dx

/--
The jet obtained by re-expanding a fixed quadratic polynomial at a new base
point.

In standard coordinates, if
`q(z) = r + p · (z - x0) + 1 / 2 (X (z - x0)) · (z - x0)`, then at `x` its
second-order part is still `X`, and its first-order part is
`p + 1 / 2 (X + Xᵀ) (x - x0)`.
-/
def quadraticModelJetAt (x0 : Point n) (p : Point n) (X : Hessian n)
    (x : Point n) : Jet n where
  gradient :=
    p + (1 / 2 : Real) •
      (Matrix.mulVec X (x - x0) + Matrix.mulVec Xᵀ (x - x0))
  hessian := X

@[simp]
theorem quadraticModelJetAt_base (x0 : Point n) (p : Point n) (X : Hessian n) :
    quadraticModelJetAt x0 p X x0 = { gradient := p, hessian := X } := by
  simp [quadraticModelJetAt]

/--
Re-expanding a quadratic model at any point gives the same polynomial.
-/
theorem quadraticModel_recenter (x0 : Point n) (r : Real) (p : Point n)
    (X : Hessian n) (x y : Point n) :
    quadraticModel x0 r p X y =
      quadraticModel x (quadraticModel x0 r p X x)
        (quadraticModelJetAt x0 p X x).gradient
        (quadraticModelJetAt x0 p X x).hessian y := by
  let a : Point n := x - x0
  let b : Point n := y - x
  have hyx0 : y - x0 = b + a := by
    ext i
    simp [a, b]
  have hcross :
      dotProduct (Matrix.mulVec X b) a =
        dotProduct (Matrix.mulVec Xᵀ a) b := by
    calc
      dotProduct (Matrix.mulVec X b) a = dotProduct a (Matrix.mulVec X b) :=
        dotProduct_comm _ _
      _ = dotProduct b (Matrix.mulVec Xᵀ a) :=
        (Matrix.dotProduct_transpose_mulVec X b a).symm
      _ = dotProduct (Matrix.mulVec Xᵀ a) b := dotProduct_comm _ _
  simp only [quadraticModel, quadraticModelJetAt]
  rw [hyx0]
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, smul_dotProduct]
  rw [hcross]
  ring

/-- The symmetric part of a Hessian matrix. -/
def symHessian (X : Hessian n) : Hessian n :=
  (1 / 2 : Real) • (X + Xᵀ)

@[simp]
theorem symHessian_apply (X : Hessian n) (i j : Fin n) :
    symHessian X i j = (1 / 2 : Real) * (X i j + X j i) :=
  rfl

/-- The symmetric part of a real Hessian is Hermitian. -/
theorem symHessian_isHermitian (X : Hessian n) :
    (symHessian X).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  simp [symHessian, add_comm]

/-- Symmetrizing a Hermitian real Hessian leaves it unchanged. -/
theorem symHessian_eq_self_of_isHermitian {X : Hessian n} (hX : X.IsHermitian) :
    symHessian X = X := by
  ext i j
  have hji : X j i = X i j := by
    simpa using hX.apply i j
  simp [symHessian, hji]
  ring

/--
The quadratic model depends only on the symmetric part of its Hessian.

This records the classical fact that `vᵀ X v = vᵀ ((X + Xᵀ) / 2) v`.
-/
theorem quadraticModel_symHessian (x0 : Point n) (r : Real) (p : Point n)
    (X : Hessian n) (x : Point n) :
    quadraticModel x0 r p (symHessian X) x =
      quadraticModel x0 r p X x := by
  let dx : Point n := x - x0
  have htranspose :
      dotProduct (Matrix.mulVec Xᵀ dx) dx =
        dotProduct (Matrix.mulVec X dx) dx := by
    calc
      dotProduct (Matrix.mulVec Xᵀ dx) dx =
          dotProduct dx (Matrix.mulVec Xᵀ dx) := dotProduct_comm _ _
      _ = dotProduct dx (Matrix.mulVec X dx) :=
          Matrix.dotProduct_transpose_mulVec X dx dx
      _ = dotProduct (Matrix.mulVec X dx) dx := dotProduct_comm _ _
  dsimp [quadraticModel, symHessian, dx]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, add_dotProduct, smul_dotProduct]
  rw [htranspose]
  ring

/-- Recentered quadratic-model gradients are unchanged by Hessian symmetrization. -/
theorem quadraticModelJetAt_gradient_symHessian
    (x0 : Point n) (p : Point n) (X : Hessian n) (x : Point n) :
    (quadraticModelJetAt x0 p (symHessian X) x).gradient =
      (quadraticModelJetAt x0 p X x).gradient := by
  ext i
  simp [quadraticModelJetAt, symHessian, Matrix.add_mulVec, Matrix.smul_mulVec]
  ring

/--
Every coordinate of a point is bounded by the finite Pi sup norm.
-/
theorem point_abs_apply_le_norm (v : Point n) (i : Fin n) : |v i| <= ‖v‖ := by
  rw [Pi.norm_def]
  have hnn : ‖v i‖₊ <= Finset.univ.sup (fun b : Fin n => ‖v b‖₊) := by
    exact Finset.le_sup (f := fun b : Fin n => ‖v b‖₊)
      (Finset.mem_univ i : i ∈ (Finset.univ : Finset (Fin n)))
  exact_mod_cast hnn

/--
The Euclidean coordinate quadratic form is controlled by the finite Pi sup norm,
with the dimension as the comparison constant.
-/
theorem dotProduct_self_le_card_mul_norm_sq (v : Point n) :
    dotProduct v v <= (n : Real) * ‖v‖ ^ 2 := by
  rw [dotProduct]
  calc
    (Finset.univ.sum fun i : Fin n => v i * v i) <=
        Finset.univ.sum fun _ : Fin n => ‖v‖ ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      have habs : |v i| <= ‖v‖ := point_abs_apply_le_norm v i
      have hsq : (v i) ^ 2 <= ‖v‖ ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg (norm_nonneg v)] using habs
      simpa [sq] using hsq
    _ = (n : Real) * ‖v‖ ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]

/--
The coordinate dot product is bounded by the product of the finite Pi norms,
up to the dimension factor.
-/
theorem abs_dotProduct_le_card_mul_norm_mul_norm (u v : Point n) :
    |dotProduct u v| <= (n : Real) * ‖u‖ * ‖v‖ := by
  rw [dotProduct]
  calc
    |∑ i : Fin n, u i * v i| <= ∑ i : Fin n, |u i * v i| := by
      exact Finset.abs_sum_le_sum_abs (fun i : Fin n => u i * v i) Finset.univ
    _ <= ∑ _i : Fin n, ‖u‖ * ‖v‖ := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      calc
        |u i * v i| = |u i| * |v i| := abs_mul _ _
        _ <= ‖u‖ * ‖v‖ := by
          gcongr
          · exact point_abs_apply_le_norm u i
          · exact point_abs_apply_le_norm v i
    _ = (n : Real) * ‖u‖ * ‖v‖ := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/--
The finite Pi sup norm is controlled by the Euclidean coordinate quadratic
form. This includes the case `n = 0`, where both sides are zero.
-/
theorem norm_sq_le_dotProduct_self (v : Point n) :
    ‖v‖ ^ 2 <= dotProduct v v := by
  have hdot_nonneg : 0 <= dotProduct v v := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _hi => by
      simpa [sq] using sq_nonneg (v i)
  have hnorm_le : ‖v‖ <= Real.sqrt (dotProduct v v) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    refine Real.le_sqrt_of_sq_le ?_
    calc
      |v i| ^ 2 = v i * v i := by
        rw [sq_abs, sq]
      _ <= ∑ j : Fin n, v j * v j := by
        exact Finset.single_le_sum
          (fun j _hj => by simpa [sq] using sq_nonneg (v j))
          (Finset.mem_univ i)
      _ = dotProduct v v := by
        simp [dotProduct]
  have hsquare := pow_le_pow_left₀ (norm_nonneg v) hnorm_le 2
  simpa [Real.sq_sqrt hdot_nonneg] using hsquare

/--
A positive scalar multiple of the identity Hessian contributes only a controlled
second-order term. The constant reflects that `Point n` uses the Pi sup norm.
-/
theorem quadraticModel_scalar_identity_bound (x0 x : Point n) {a : Real} (ha : 0 <= a) :
    quadraticModel x0 0 0 (a • (1 : Hessian n)) x <=
      ((1 / 2 : Real) * a * (n : Real)) * ‖x - x0‖ ^ 2 := by
  let dx : Point n := x - x0
  have hdot : dotProduct dx dx <= (n : Real) * ‖dx‖ ^ 2 :=
    dotProduct_self_le_card_mul_norm_sq dx
  have hmul : (1 / 2 : Real) * a * dotProduct dx dx <=
      (1 / 2 : Real) * a * ((n : Real) * ‖dx‖ ^ 2) := by
    gcongr
  calc
    quadraticModel x0 0 0 (a • (1 : Hessian n)) x =
        (1 / 2 : Real) * a * dotProduct dx dx := by
      simp [quadraticModel, dx, Matrix.smul_mulVec, Matrix.one_mulVec, smul_dotProduct]
      ring
    _ <= (1 / 2 : Real) * a * ((n : Real) * ‖dx‖ ^ 2) := hmul
    _ = ((1 / 2 : Real) * a * (n : Real)) * ‖x - x0‖ ^ 2 := by
      simp [dx]
      ring

/--
A positive scalar multiple of the identity Hessian dominates the square of the
finite Pi sup norm, with coefficient `a / 2`.
-/
theorem quadraticModel_scalar_identity_lower_bound (x0 x : Point n) {a : Real}
    (ha : 0 <= a) :
    ((1 / 2 : Real) * a) * ‖x - x0‖ ^ 2 <=
      quadraticModel x0 0 0 (a • (1 : Hessian n)) x := by
  let dx : Point n := x - x0
  have hdot : ‖dx‖ ^ 2 <= dotProduct dx dx := norm_sq_le_dotProduct_self dx
  have hmul : ((1 / 2 : Real) * a) * ‖dx‖ ^ 2 <=
      ((1 / 2 : Real) * a) * dotProduct dx dx := by
    gcongr
  calc
    ((1 / 2 : Real) * a) * ‖x - x0‖ ^ 2 =
        ((1 / 2 : Real) * a) * ‖dx‖ ^ 2 := by simp [dx]
    _ <= ((1 / 2 : Real) * a) * dotProduct dx dx := hmul
    _ = quadraticModel x0 0 0 (a • (1 : Hessian n)) x := by
      simp [quadraticModel, dx, Matrix.smul_mulVec, Matrix.one_mulVec, smul_dotProduct]
      ring

/-- Evaluation at a Hessian entry is continuous. -/
theorem continuous_hessian_apply_apply (i j : Fin n) :
    Continuous fun X : Hessian n => X i j := by
  exact (continuous_apply j).comp (continuous_apply i)

/--
For every `η > 0`, the set of matrices `Y` such that
`|(Y - X) i j| < η` for all entries `i j` is a neighborhood of `X`. This
packages the product topology on `Hessian n` into the finite entrywise form
used by semijet closure arguments.
-/
theorem hessian_eventually_entrywise_abs_sub_lt (X : Hessian n) {η : Real} (hη : 0 < η) :
    ∀ᶠ Y in nhds X, ∀ i j : Fin n, |(Y - X) i j| < η := by
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  have hcont : Continuous fun Y : Hessian n => Y i j :=
    continuous_hessian_apply_apply i j
  have htarget : ∀ᶠ z in nhds (X i j), |z - X i j| < η := by
    exact Metric.eventually_nhds_iff.mpr ⟨η, hη, fun z hz => by rwa [Real.dist_eq] at hz⟩
  have hpre := (hcont.continuousAt).eventually htarget
  simpa [Pi.sub_apply] using hpre

/--
If a Hessian has all entries bounded by `η`, then its quadratic model is
bounded by a dimension-dependent multiple of `η ‖x - x0‖²`.
-/
theorem abs_quadraticModel_zero_zero_le_of_entrywise_abs_le (x0 x : Point n)
    {A : Hessian n} {η : Real} (_hη : 0 <= η)
    (hA : ∀ i j : Fin n, |A i j| <= η) :
    |quadraticModel x0 0 0 A x| <=
      ((1 / 2 : Real) * η * (n : Real) * (n : Real)) * ‖x - x0‖ ^ 2 := by
  let dx : Point n := x - x0
  have hterm (i j : Fin n) : |A i j * dx j * dx i| <= η * ‖dx‖ * ‖dx‖ := by
    calc
      |A i j * dx j * dx i| = |A i j| * |dx j| * |dx i| := by
        rw [abs_mul, abs_mul]
      _ <= η * ‖dx‖ * ‖dx‖ := by
        gcongr
        · exact hA i j
        · exact point_abs_apply_le_norm dx j
        · exact point_abs_apply_le_norm dx i
  have hsum : |dotProduct (Matrix.mulVec A dx) dx| <=
      (n : Real) * ((n : Real) * (η * ‖dx‖ * ‖dx‖)) := by
    calc
      |dotProduct (Matrix.mulVec A dx) dx| =
          |∑ i : Fin n, ∑ j : Fin n, A i j * dx j * dx i| := by
        simp [dotProduct, Matrix.mulVec, Finset.sum_mul, mul_assoc]
      _ <= ∑ i : Fin n, |∑ j : Fin n, A i j * dx j * dx i| := by
        simpa using Finset.abs_sum_le_sum_abs
          (fun i : Fin n => ∑ j : Fin n, A i j * dx j * dx i) Finset.univ
      _ <= ∑ _i : Fin n, ∑ _j : Fin n, η * ‖dx‖ * ‖dx‖ := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        calc
          |∑ j : Fin n, A i j * dx j * dx i| <=
              ∑ j : Fin n, |A i j * dx j * dx i| := by
            simpa using Finset.abs_sum_le_sum_abs
              (fun j : Fin n => A i j * dx j * dx i) Finset.univ
          _ <= ∑ _j : Fin n, η * ‖dx‖ * ‖dx‖ := by
            refine Finset.sum_le_sum ?_
            intro j _hj
            exact hterm i j
      _ = (n : Real) * ((n : Real) * (η * ‖dx‖ * ‖dx‖)) := by
        simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  calc
    |quadraticModel x0 0 0 A x| =
        |(1 / 2 : Real) * dotProduct (Matrix.mulVec A dx) dx| := by
      simp [quadraticModel, dx]
    _ = (1 / 2 : Real) * |dotProduct (Matrix.mulVec A dx) dx| := by
      rw [abs_mul, abs_of_nonneg]
      norm_num
    _ <= (1 / 2 : Real) * ((n : Real) * ((n : Real) * (η * ‖dx‖ * ‖dx‖))) := by
      gcongr
    _ = ((1 / 2 : Real) * η * (n : Real) * (n : Real)) * ‖x - x0‖ ^ 2 := by
      simp [dx, sq]
      ring

/--
For fixed base point, value, and evaluation point, the quadratic model varies
continuously with the jet data.
-/
theorem continuous_quadraticModel_jet (x0 : Point n) (r : Real) (x : Point n) :
    Continuous fun J : Jet n => quadraticModel x0 r J.gradient J.hessian x := by
  let dx : Point n := x - x0
  have hdx : Continuous fun _ : Jet n => dx := continuous_const
  have hlin : Continuous fun J : Jet n => dotProduct J.gradient dx :=
    Jet.continuous_gradient.dotProduct hdx
  have hquad : Continuous fun J : Jet n => dotProduct (Matrix.mulVec J.hessian dx) dx := by
    exact (Jet.continuous_hessian.matrix_mulVec hdx).dotProduct hdx
  have htotal : Continuous fun J : Jet n =>
      r + dotProduct J.gradient dx + (1 / 2 : Real) * dotProduct (Matrix.mulVec J.hessian dx) dx :=
    (continuous_const.add hlin).add (continuous_const.mul hquad)
  simpa [quadraticModel, dx, add_assoc] using htotal

/--
For fixed jet data, the quadratic model is a continuous function of the
evaluation point.
-/
theorem continuous_quadraticModel (x0 : Point n) (r : Real) (p : Point n)
    (X : Hessian n) :
    Continuous fun x : Point n => quadraticModel x0 r p X x := by
  let dx : Point n -> Point n := fun x => x - x0
  have hdx : Continuous dx := continuous_id.sub continuous_const
  have hlin : Continuous fun x : Point n => dotProduct p (dx x) :=
    continuous_const.dotProduct hdx
  have hX : Continuous fun _x : Point n => (X : Hessian n) := continuous_const
  have hquad : Continuous fun x : Point n => dotProduct (Matrix.mulVec X (dx x)) (dx x) :=
    (hX.matrix_mulVec hdx).dotProduct hdx
  have htotal : Continuous fun x : Point n =>
      r + dotProduct p (dx x) + (1 / 2 : Real) * dotProduct (Matrix.mulVec X (dx x)) (dx x) :=
    (continuous_const.add hlin).add (continuous_const.mul hquad)
  simpa [quadraticModel, dx, add_assoc] using htotal

/-- Negating the value, gradient, and Hessian data negates the quadratic model. -/
@[simp]
theorem quadraticModel_neg (x0 : Point n) (r : Real) (p : Point n) (X : Hessian n)
    (x : Point n) : quadraticModel x0 (-r) (-p) (-X) x = -quadraticModel x0 r p X x := by
  simp only [quadraticModel, Matrix.neg_mulVec, neg_dotProduct]
  ring

/-- The quadratic model is additive in its value, gradient, and Hessian data. -/
theorem quadraticModel_add (x0 : Point n) (r s : Real) (p q : Point n) (X Y : Hessian n)
    (x : Point n) :
    quadraticModel x0 (r + s) (p + q) (X + Y) x =
      quadraticModel x0 r p X x + quadraticModel x0 s q Y x := by
  simp only [quadraticModel, Matrix.add_mulVec, add_dotProduct]
  ring

/-- The quadratic model is subtractive in its value, gradient, and Hessian data. -/
theorem quadraticModel_sub (x0 : Point n) (r s : Real) (p q : Point n) (X Y : Hessian n)
    (x : Point n) :
    quadraticModel x0 (r - s) (p - q) (X - Y) x =
      quadraticModel x0 r p X x - quadraticModel x0 s q Y x := by
  simp only [quadraticModel, Matrix.sub_mulVec, sub_dotProduct]
  ring

/--
The mixed second difference of a quadratic model depends only on the Hessian.

In standard mathematical terms, for a quadratic polynomial
`q(x) = r + p · (x - x0) + (1 / 2)⟪X(x - x0), x - x0⟫`, the expression

`q(x0 + u + v) - q(x0 + u) - q(x0 + v) + q(x0)`

is

`(1 / 2) * (⟪Xu, v⟫ + ⟪Xv, u⟫)`.
-/
theorem quadraticModel_mixed_second_difference (x0 : Point n) (r : Real)
    (p : Point n) (X : Hessian n) (u v : Point n) :
    quadraticModel x0 r p X (x0 + u + v) -
        quadraticModel x0 r p X (x0 + u) -
        quadraticModel x0 r p X (x0 + v) +
        quadraticModel x0 r p X x0 =
      (1 / 2 : Real) *
        (dotProduct (Matrix.mulVec X u) v + dotProduct (Matrix.mulVec X v) u) := by
  simp only [quadraticModel]
  have h₁ : x0 + u + v - x0 = u + v := by
    ext i
    change x0 i + u i + v i - x0 i = u i + v i
    ring
  have h₂ : x0 + u - x0 = u := by
    ext i
    change x0 i + u i - x0 i = u i
    ring
  have h₃ : x0 + v - x0 = v := by
    ext i
    change x0 i + v i - x0 i = v i
    ring
  simp only [h₁, h₂, h₃, sub_self, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  simp [dotProduct]
  ring

/--
The quadratic model is affine in its jet data when the base value is fixed.
-/
theorem quadraticModel_convexCombination (x0 : Point n) (r a b : Real) (p q : Point n)
    (X Y : Hessian n) (x : Point n) (hab : a + b = 1) :
    quadraticModel x0 r (a • p + b • q) (a • X + b • Y) x =
      a * quadraticModel x0 r p X x + b * quadraticModel x0 r q Y x := by
  have hr : r * a + r * b = r := by
    nlinarith [congrArg (fun t => r * t) hab]
  simp only [quadraticModel, Matrix.add_mulVec, Matrix.smul_mulVec, add_dotProduct,
    smul_dotProduct]
  ring_nf at hr ⊢
  nlinarith

/-- The quadratic model is monotone in the Hessian for the Loewner order. -/
theorem quadraticModel_le_of_hessian_le {x0 : Point n} {r : Real} {p : Point n}
    {X Y : Hessian n} (hXY : X <= Y) (x : Point n) :
    quadraticModel x0 r p X x <= quadraticModel x0 r p Y x := by
  let dx : Point n := x - x0
  have hnonneg : 0 <= dotProduct dx (Matrix.mulVec (Y - X) dx) := by
    have hpsd : (Y - X).PosSemidef := Matrix.le_iff.mp hXY
    simpa using hpsd.dotProduct_mulVec_nonneg dx
  have hquad :
      dotProduct (Matrix.mulVec X dx) dx <= dotProduct (Matrix.mulVec Y dx) dx := by
    have hrewrite : dotProduct dx (Matrix.mulVec (Y - X) dx) =
        dotProduct (Matrix.mulVec Y dx) dx - dotProduct (Matrix.mulVec X dx) dx := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
      rw [dotProduct_comm dx (Y *ᵥ dx), dotProduct_comm dx (X *ᵥ dx)]
    linarith
  dsimp [quadraticModel]
  change r + dotProduct p dx + (1 / 2 : Real) * dotProduct (Matrix.mulVec X dx) dx <=
    r + dotProduct p dx + (1 / 2 : Real) * dotProduct (Matrix.mulVec Y dx) dx
  linarith

/--
The little-oh remainder used in the definition of second-order semijets,
relative to a domain `C`.
-/
def SemijetRemainder (C : Set (Point n)) (x0 : Point n) (rho : Point n -> Real) : Prop :=
  Asymptotics.IsLittleO (nhdsWithin x0 C) rho (fun x : Point n => ‖x - x0‖ ^ 2)

theorem semijetRemainder_congr_nhdsWithin {C D : Set (Point n)} {x0 : Point n}
    {rho : Point n -> Real} (h : nhdsWithin x0 C = nhdsWithin x0 D) :
    SemijetRemainder C x0 rho ↔ SemijetRemainder D x0 rho := by
  simp [SemijetRemainder, h]

theorem semijetRemainder_add {C : Set (Point n)} {x0 : Point n}
    {rho sigma : Point n -> Real}
    (hrho : SemijetRemainder C x0 rho) (hsigma : SemijetRemainder C x0 sigma) :
    SemijetRemainder C x0 (fun x => rho x + sigma x) :=
  Asymptotics.IsLittleO.add hrho hsigma

theorem semijetRemainder_neg {C : Set (Point n)} {x0 : Point n}
    {rho : Point n -> Real} (hrho : SemijetRemainder C x0 rho) :
    SemijetRemainder C x0 (fun x => -rho x) :=
  hrho.neg_left

theorem semijetRemainder_sub {C : Set (Point n)} {x0 : Point n}
    {rho sigma : Point n -> Real}
    (hrho : SemijetRemainder C x0 rho) (hsigma : SemijetRemainder C x0 sigma) :
    SemijetRemainder C x0 (fun x => rho x - sigma x) := by
  simpa [sub_eq_add_neg] using semijetRemainder_add hrho (semijetRemainder_neg hsigma)

theorem semijetRemainder_const_mul {C : Set (Point n)} {x0 : Point n}
    {rho : Point n -> Real} (a : Real)
    (hrho : SemijetRemainder C x0 rho) :
    SemijetRemainder C x0 (fun x => a * rho x) :=
  Asymptotics.IsLittleO.const_mul_left hrho a

/--
A second-order remainder remains `o(t^2)` along every affine line through its
base point.

In standard mathematical terms, if `ρ(w) = o(|w - z|^2)` as `w -> z`, then
for every vector `a`,

`ρ(z + t a) = o(t^2)` as `t -> 0`.
-/
theorem semijetRemainder_along_affine_isLittleO_sq
    {rho : Point n -> Real} {z a : Point n}
    (hrho : SemijetRemainder Set.univ z rho) :
    Asymptotics.IsLittleO (nhds (0 : Real)) (fun t : Real => rho (z + t • a))
      (fun t : Real => t ^ 2) := by
  have hline : Tendsto (fun t : Real => z + t • a) (nhds (0 : Real)) (nhds z) := by
    have hcont : ContinuousAt (fun t : Real => z + t • a) 0 :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    simpa [ContinuousAt] using hcont
  have hrho_nhds :
      Asymptotics.IsLittleO (nhds z) rho (fun x : Point n => ‖x - z‖ ^ 2) := by
    simpa [SemijetRemainder, nhdsWithin_univ] using hrho
  have hcomp : Asymptotics.IsLittleO (nhds (0 : Real))
      (fun t : Real => rho (z + t • a))
      (fun t : Real => ‖(z + t • a) - z‖ ^ 2) :=
    hrho_nhds.comp_tendsto hline
  have hbig : (fun t : Real => ‖(z + t • a) - z‖ ^ 2) =O[nhds (0 : Real)]
      (fun t : Real => t ^ 2) := by
    refine Asymptotics.IsBigO.of_bound (‖a‖ ^ 2) (Eventually.of_forall ?_)
    intro t
    have hsub : z + t • a - z = t • a := by
      ext i
      simp
    rw [hsub]
    rw [norm_smul]
    simp [Real.norm_eq_abs, mul_pow, sq_abs, mul_comm]
  exact hcomp.trans_isBigO hbig

/--
The mixed second difference of a second-order remainder is `o(t^2)` along
two fixed directions.

In standard mathematical terms, if `ρ(w) = o(|w - z|^2)` as `w -> z` and
`ρ(z) = 0`, then for all vectors `u` and `v`,

`ρ(z + t u + t v) - ρ(z + t u) - ρ(z + t v) + ρ(z) = o(t^2)`.
-/
theorem semijetRemainder_mixed_along_affine_isLittleO_sq
    {rho : Point n -> Real} {z u v : Point n}
    (hrho : SemijetRemainder Set.univ z rho) (hrho_z : rho z = 0) :
    Asymptotics.IsLittleO (nhds (0 : Real))
      (fun t : Real => rho (z + t • u + t • v) - rho (z + t • u) -
        rho (z + t • v) + rho z)
      (fun t : Real => t ^ 2) := by
  have hboth : Asymptotics.IsLittleO (nhds (0 : Real))
      (fun t : Real => rho (z + t • (u + v))) (fun t : Real => t ^ 2) :=
    semijetRemainder_along_affine_isLittleO_sq (n := n) (z := z) (a := u + v) hrho
  have hboth' : Asymptotics.IsLittleO (nhds (0 : Real))
      (fun t : Real => rho (z + t • u + t • v)) (fun t : Real => t ^ 2) := by
    simpa [smul_add, add_assoc] using hboth
  have hleft : Asymptotics.IsLittleO (nhds (0 : Real))
      (fun t : Real => rho (z + t • u)) (fun t : Real => t ^ 2) :=
    semijetRemainder_along_affine_isLittleO_sq (n := n) (z := z) (a := u) hrho
  have hright : Asymptotics.IsLittleO (nhds (0 : Real))
      (fun t : Real => rho (z + t • v)) (fun t : Real => t ^ 2) :=
    semijetRemainder_along_affine_isLittleO_sq (n := n) (z := z) (a := v) hrho
  have hconst : Asymptotics.IsLittleO (nhds (0 : Real))
      (fun _t : Real => rho z) (fun t : Real => t ^ 2) := by
    simp [hrho_z]
  exact (hboth'.sub hleft).sub hright |>.add hconst

/--
`φ` has second-order expansion with prescribed value `r` and jet `J`, relative to
the domain `C`.
-/
def HasSecondOrderExpansionWithinAtValue (C : Set (Point n)) (φ : Point n -> Real)
    (x0 : Point n) (r : Real) (J : Jet n) : Prop :=
  exists rho : Point n -> Real,
    SemijetRemainder C x0 rho /\
      Filter.Eventually
        (fun x : Point n =>
          φ x = quadraticModel x0 r J.gradient J.hessian x + rho x)
        (nhdsWithin x0 C)

/--
The remainder in a second-order expansion has the forced value at the base
point.

In standard mathematical terms, if

`φ(x) = r + p · (x - x₀) + (1 / 2)⟪X(x - x₀), x - x₀⟫ + ρ(x)`

for all `x` sufficiently close to `x₀` inside `C`, and if `x₀ ∈ C`, then
`ρ(x₀) = φ(x₀) - r`.
-/
theorem secondOrderExpansion_remainder_at_base
    {C : Set (Point n)} {φ rho : Point n -> Real} {x0 : Point n}
    {r : Real} {J : Jet n} (hx0 : x0 ∈ C)
    (hφ : Filter.Eventually
        (fun x : Point n =>
          φ x = quadraticModel x0 r J.gradient J.hessian x + rho x)
        (nhdsWithin x0 C)) :
    rho x0 = φ x0 - r := by
  have hbase := hφ.self_of_nhdsWithin hx0
  simp [quadraticModel] at hbase
  linarith

/--
For an expansion whose prescribed value is the value of the function at the
base point, the remainder vanishes at the base point.
-/
theorem secondOrderExpansion_remainder_eq_zero_at_base
    {C : Set (Point n)} {φ rho : Point n -> Real} {x0 : Point n}
    {J : Jet n} (hx0 : x0 ∈ C)
    (hφ : Filter.Eventually
        (fun x : Point n =>
          φ x = quadraticModel x0 (φ x0) J.gradient J.hessian x + rho x)
        (nhdsWithin x0 C)) :
    rho x0 = 0 := by
  have h := secondOrderExpansion_remainder_at_base
    (C := C) (φ := φ) (rho := rho) (x0 := x0) (r := φ x0) (J := J) hx0 hφ
  simpa using h

theorem hasSecondOrderExpansionWithinAtValue_congr_nhdsWithin
    {C D : Set (Point n)} {φ : Point n -> Real} {x0 : Point n}
    {r : Real} {J : Jet n} (h : nhdsWithin x0 C = nhdsWithin x0 D) :
    HasSecondOrderExpansionWithinAtValue C φ x0 r J ↔
      HasSecondOrderExpansionWithinAtValue D φ x0 r J := by
  constructor
  · rintro ⟨rho, hrho, hφ⟩
    exact ⟨rho, (semijetRemainder_congr_nhdsWithin h).1 hrho, by simpa [h] using hφ⟩
  · rintro ⟨rho, hrho, hφ⟩
    exact ⟨rho, (semijetRemainder_congr_nhdsWithin h.symm).1 hrho,
      by simpa [h.symm] using hφ⟩

/--
`φ` has second-order expansion at `x0` with jet `J`, relative to the domain `C`.

This is the abstraction used for smooth test functions: later, a Taylor theorem
for `C^2` functions can be used to build this predicate from differentiability
data.
-/
def HasSecondOrderExpansionWithin (C : Set (Point n)) (φ : Point n -> Real)
    (x0 : Point n) (J : Jet n) : Prop :=
  HasSecondOrderExpansionWithinAtValue C φ x0 (φ x0) J

theorem hasSecondOrderExpansionWithin_congr_nhdsWithin
    {C D : Set (Point n)} {φ : Point n -> Real} {x0 : Point n}
    {J : Jet n} (h : nhdsWithin x0 C = nhdsWithin x0 D) :
    HasSecondOrderExpansionWithin C φ x0 J ↔
      HasSecondOrderExpansionWithin D φ x0 J :=
  hasSecondOrderExpansionWithinAtValue_congr_nhdsWithin h

/--
The recentered jet of a quadratic model gives an exact second-order expansion.

A quadratic polynomial has zero Taylor remainder when it is expanded at any
point, with the recentered jet `quadraticModelJetAt`.
-/
theorem hasSecondOrderExpansionWithin_quadraticModel_recenter
    {C : Set (Point n)} (x0 : Point n) (r : Real) (p : Point n)
    (X : Hessian n) (x : Point n) :
    HasSecondOrderExpansionWithin C
      (fun y => quadraticModel x0 r p X y) x
      (quadraticModelJetAt x0 p X x) := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · simp [SemijetRemainder]
  · exact Eventually.of_forall fun y => by
      simpa using quadraticModel_recenter x0 r p X x y

theorem continuous_quadraticModelJetAt (x0 : Point n) (p : Point n)
    (X : Hessian n) :
    Continuous fun x : Point n => quadraticModelJetAt x0 p X x := by
  have hdx : Continuous fun x : Point n => x - x0 := continuous_id.sub continuous_const
  have hX : Continuous fun _x : Point n => (X : Hessian n) := continuous_const
  have hXt : Continuous fun _x : Point n => (Xᵀ : Hessian n) := continuous_const
  have hgrad : Continuous fun x : Point n =>
      p + (1 / 2 : Real) • (Matrix.mulVec X (x - x0) + Matrix.mulVec Xᵀ (x - x0)) :=
    continuous_const.add (((hX.matrix_mulVec hdx).add (hXt.matrix_mulVec hdx)).const_smul
      (1 / 2 : Real))
  apply continuous_induced_rng.mpr
  change Continuous fun x : Point n =>
    ((quadraticModelJetAt x0 p X x).gradient, (quadraticModelJetAt x0 p X x).hessian)
  simpa [quadraticModelJetAt] using Continuous.prodMk hgrad hX

/--
As `x -> 0`, the gradient component of the recentered quadratic model with
base point `0` and first-order component `0` tends to `0`.
-/
theorem tendsto_quadraticModelJetAt_zero_zero_gradient_zero (X : Hessian n) :
    Filter.Tendsto (fun x : Point n =>
      (quadraticModelJetAt (0 : Point n) 0 X x).gradient)
      (nhds (0 : Point n)) (nhds (0 : Point n)) := by
  have hcont :
      Continuous fun x : Point n =>
        (quadraticModelJetAt (0 : Point n) 0 X x).gradient :=
    Jet.continuous_gradient.comp
      (continuous_quadraticModelJetAt (0 : Point n) 0 X)
  have hz :
      (quadraticModelJetAt (0 : Point n) 0 X (0 : Point n)).gradient =
        (0 : Point n) := by
    simp
  have h0 :
      ContinuousAt
        (fun x : Point n => (quadraticModelJetAt (0 : Point n) 0 X x).gradient)
        (0 : Point n) :=
    hcont.continuousAt
  simpa [hz] using h0.tendsto

/-- `φ` touches `u` from above at `x0`, relative to `C`. -/
def TouchesAboveOn (C : Set (Point n)) (u φ : Point n -> Real) (x0 : Point n) : Prop :=
  Filter.Eventually
    (fun x : Point n => u x - φ x <= u x0 - φ x0)
    (nhdsWithin x0 C)

theorem touchesAboveOn_congr_nhdsWithin
    {C D : Set (Point n)} {u φ : Point n -> Real} {x0 : Point n}
    (h : nhdsWithin x0 C = nhdsWithin x0 D) :
    TouchesAboveOn C u φ x0 ↔ TouchesAboveOn D u φ x0 := by
  simp [TouchesAboveOn, h]

/-- `φ` touches `u` from below at `x0`, relative to `C`. -/
def TouchesBelowOn (C : Set (Point n)) (u φ : Point n -> Real) (x0 : Point n) : Prop :=
  Filter.Eventually
    (fun x : Point n => u x0 - φ x0 <= u x - φ x)
    (nhdsWithin x0 C)

theorem touchesBelowOn_congr_nhdsWithin
    {C D : Set (Point n)} {u φ : Point n -> Real} {x0 : Point n}
    (h : nhdsWithin x0 C = nhdsWithin x0 D) :
    TouchesBelowOn C u φ x0 ↔ TouchesBelowOn D u φ x0 := by
  simp [TouchesBelowOn, h]

end ViscositySolns
