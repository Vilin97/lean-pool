/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatCutoff
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothCovariance

/-!
# Covariance amplitudes across an exponential-flat edge

The normalized matrix and target are actual smooth functions with an explicit
strict cone. Columns are then multiplied by `edge κᵢ`, and the target by
`edge σ`. Exact inverse and square-root identities exhibit a positive remaining
exponential whenever `κᵢ < σ`; in particular the squared-factor convention
`κᵢ = 2 λᵢ` is covered by `λᵢ < σ / 2`.

The coefficient quotients are proved smooth from these formulas. Their
smoothness across the singular matrix at the edge is not assumed.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.FlatCovariance

open Matrix Set
open SmoothCovariance (Mat2 Vec2)
open FlatCutoff (edge)
open scoped ContDiff Topology

/-- Multiplication of column `j` by its scalar factor `c j`. -/
def columns (G : Mat2) (c : Vec2) : Mat2 := fun i j => c j * G i j

/-- Scaled target, defined pointwise by `r * T i`. -/
def scaledTarget (r : ℝ) (T : Vec2) : Vec2 := fun i => r * T i

/-- The actual edge-degenerate covariance matrix. -/
def edgeMatrix (κ : Vec2) (G : ℝ → Mat2) (x : ℝ) : Mat2 :=
  columns (G x) (fun j => edge (κ j) x)

/-- Edge target, given by `scaledTarget (edge σ x) (T x)`. -/
def edgeTarget (σ : ℝ) (T : ℝ → Vec2) (x : ℝ) : Vec2 :=
  scaledTarget (edge σ x) (T x)

/-- The actual matrix-inverse solve, also defined at the zero edge. -/
def inverseCoefficients (σ : ℝ) (κ : Vec2) (G : ℝ → Mat2) (T : ℝ → Vec2)
    (x : ℝ) : Vec2 :=
  (edgeMatrix κ G x)⁻¹.mulVec (edgeTarget σ T x)

/-- Primary amplitude, defined pointwise by `Real.sqrt (inverseCoefficients σ κ G T x i)`. -/
def primaryAmplitude (σ : ℝ) (κ : Vec2) (G : ℝ → Mat2) (T : ℝ → Vec2)
    (x : ℝ) : Vec2 :=
  fun i => Real.sqrt (inverseCoefficients σ κ G T x i)

/-- The signed covariance update divides by the fixed positive primary. -/
def signedAmplitude (σ τ : ℝ) (κ : Vec2) (G : ℝ → Mat2)
    (T R : ℝ → Vec2) (x : ℝ) : Vec2 :=
  fun i => inverseCoefficients τ κ G R x i / (2 * primaryAmplitude σ κ G T x i)

theorem sqrt_edge (c x : ℝ) : Real.sqrt (edge c x) = edge (c / 2) x := by
  by_cases hx : x ≤ 0
  · simp [FlatCutoff.edge_of_nonpos c hx, FlatCutoff.edge_of_nonpos (c / 2) hx]
  · have hp : 0 < x := lt_of_not_ge hx
    rw [FlatCutoff.edge_of_pos c hp, FlatCutoff.edge_of_pos (c / 2) hp,
      ← Real.exp_half]
    congr 1
    ring

theorem edge_mul (c d x : ℝ) : edge c x * edge d x = edge (c + d) x := by
  by_cases hx : x ≤ 0
  · simp [FlatCutoff.edge_of_nonpos c hx, FlatCutoff.edge_of_nonpos d hx,
      FlatCutoff.edge_of_nonpos (c + d) hx]
  · have hp : 0 < x := lt_of_not_ge hx
    rw [FlatCutoff.edge_of_pos c hp, FlatCutoff.edge_of_pos d hp,
      FlatCutoff.edge_of_pos (c + d) hp, ← Real.exp_add]
    congr 1
    ring

theorem edge_sq (c x : ℝ) : edge c x ^ 2 = edge (2 * c) x := by
  rw [pow_two, edge_mul]
  congr 1
  ring

theorem squared_column_factors (lam : Vec2) (G : ℝ → Mat2) (x : ℝ) :
    columns (G x) (fun j => edge (lam j) x ^ 2) =
      edgeMatrix (fun j => 2 * lam j) G x := by
  ext i j
  simp only [columns, edgeMatrix, edge_sq]

theorem determinant_columns (G : Mat2) (c : Vec2) :
    (columns G c).det = c 0 * c 1 * G.det := by
  simp only [Matrix.det_fin_two, columns]
  ring

theorem columns_det_ne_zero {G : Mat2} {c : Vec2}
    (hG : G.det ≠ 0) (hc : ∀ i, c i ≠ 0) : (columns G c).det ≠ 0 := by
  rw [determinant_columns]
  exact mul_ne_zero (mul_ne_zero (hc 0) (hc 1)) hG

/-- Cramer's formula records the exact effect of individual column factors. -/
theorem weights_columns (G : Mat2) (c : Vec2) (T : Vec2) (r : ℝ)
    (hG : G.det ≠ 0) (hc : ∀ i, c i ≠ 0) (i : Fin 2) :
    SmoothCovariance.weights (columns G c) (scaledTarget r T) i =
      (r / c i) * SmoothCovariance.weights G T i := by
  have hc0 := hc 0
  have hc1 := hc 1
  fin_cases i <;>
    simp only [SmoothCovariance.weights, determinant_columns,
      SmoothCovariance.cramerNumerator, columns, scaledTarget,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one] <;>
    field_simp

theorem edgeMatrix_det_ne_zero {κ : Vec2} {G : ℝ → Mat2} {x : ℝ}
    (hG : (G x).det ≠ 0) (hx : 0 < x) : (edgeMatrix κ G x).det ≠ 0 :=
  columns_det_ne_zero hG (fun i => ne_of_gt (FlatCutoff.edge_pos (κ i) hx))

theorem inverseCoefficients_of_nonpos (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) {x : ℝ} (hx : x ≤ 0) :
    inverseCoefficients σ κ G T x = 0 := by
  have ht : edgeTarget σ T x = 0 := by
    ext i
    simp [edgeTarget, scaledTarget, FlatCutoff.edge_of_nonpos σ hx]
  simp [inverseCoefficients, ht]

theorem primaryAmplitude_of_nonpos (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) {x : ℝ} (hx : x ≤ 0) (i : Fin 2) :
    primaryAmplitude σ κ G T x i = 0 := by
  simp [primaryAmplitude, inverseCoefficients_of_nonpos σ κ G T hx]

theorem signedAmplitude_of_nonpos (σ τ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T R : ℝ → Vec2) {x : ℝ} (hx : x ≤ 0) (i : Fin 2) :
    signedAmplitude σ τ κ G T R x i = 0 := by
  simp [signedAmplitude, inverseCoefficients_of_nonpos τ κ G R hx]

/-- Exact cancellation of the column exponential in the actual inverse.
This identity includes the edge and the full zero half-line. -/
theorem inverseCoefficients_factor (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) {x : ℝ} (hG : (G x).det ≠ 0) (i : Fin 2) :
    inverseCoefficients σ κ G T x i =
      edge (σ - κ i) x * SmoothCovariance.weights (G x) (T x) i := by
  by_cases hx : x ≤ 0
  · simp [inverseCoefficients_of_nonpos σ κ G T hx,
      FlatCutoff.edge_of_nonpos (σ - κ i) hx]
  · have hp : 0 < x := lt_of_not_ge hx
    have hs := SmoothCovariance.inverse_formula (edgeMatrix κ G x) (edgeTarget σ T x)
      (edgeMatrix_det_ne_zero hG hp)
    change ((edgeMatrix κ G x)⁻¹.mulVec (edgeTarget σ T x)) i = _
    rw [hs]
    dsimp only [edgeMatrix, edgeTarget]
    rw [weights_columns (G x) (fun j => edge (κ j) x) (T x) (edge σ x) hG
      (fun j => ne_of_gt (FlatCutoff.edge_pos (κ j) hp)) i]
    rw [congrFun (FlatCutoff.edge_div_edge σ (κ i)) x]

/-- Taking the square root halves the *remaining* exponential exponent. -/
theorem primaryAmplitude_factor (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) {x : ℝ} (hG : (G x).det ≠ 0) (i : Fin 2) :
    primaryAmplitude σ κ G T x i = edge ((σ - κ i) / 2) x *
      SmoothCovariance.amplitudes (G x) (T x) i := by
  unfold primaryAmplitude
  rw [inverseCoefficients_factor σ κ G T hG i,
    Real.sqrt_mul (FlatCutoff.edge_nonneg (σ - κ i) x), sqrt_edge]
  rfl

/-- The signed update retains the explicitly computed exponential margin;
the target `R` may have either sign. -/
theorem signedAmplitude_factor (σ τ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T R : ℝ → Vec2) {x : ℝ} (hG : (G x).det ≠ 0) (i : Fin 2) :
    signedAmplitude σ τ κ G T R x i = edge (τ - (σ + κ i) / 2) x *
      (SmoothCovariance.weights (G x) (R x) i /
        (2 * SmoothCovariance.amplitudes (G x) (T x) i)) := by
  unfold signedAmplitude
  rw [inverseCoefficients_factor τ κ G R hG i, primaryAmplitude_factor σ κ G T hG i]
  calc
    _ = (edge (τ - κ i) x / edge ((σ - κ i) / 2) x) *
        (SmoothCovariance.weights (G x) (R x) i /
          (2 * SmoothCovariance.amplitudes (G x) (T x) i)) := by
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
      ring
    _ = _ := by
      rw [congrFun (FlatCutoff.edge_div_edge (τ - κ i) ((σ - κ i) / 2)) x]
      congr 2
      ring

/-- Exact linearity in a scalar target factor, with no regularity or
nonvanishing assumption on that factor. -/
theorem inverseCoefficients_target_factor (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) (f : ℝ → ℝ) (x : ℝ) (i : Fin 2) :
    inverseCoefficients σ κ G (fun y j => f y * T y j) x i =
      f x * inverseCoefficients σ κ G T x i := by
  simp only [inverseCoefficients, edgeTarget, scaledTarget, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  ring

theorem signedAmplitude_target_factor (σ τ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T R : ℝ → Vec2) (f : ℝ → ℝ) (x : ℝ) (i : Fin 2) :
    signedAmplitude σ τ κ G T (fun y j => f y * R y j) x i =
      f x * signedAmplitude σ τ κ G T R x i := by
  unfold signedAmplitude
  rw [inverseCoefficients_target_factor]
  ring

theorem inverseCoefficients_pos {σ : ℝ} {κ : Vec2}
    {G : ℝ → Mat2} {T : ℝ → Vec2} {x : ℝ}
    (hcone : SmoothCovariance.StrictCone (G x) (T x)) (hx : 0 < x) (i : Fin 2) :
    0 < inverseCoefficients σ κ G T x i := by
  rw [inverseCoefficients_factor σ κ G T hcone.det_ne_zero i]
  exact mul_pos (FlatCutoff.edge_pos _ hx) (hcone.weights_pos i)

theorem primaryAmplitude_pos {σ : ℝ} {κ : Vec2}
    {G : ℝ → Mat2} {T : ℝ → Vec2} {x : ℝ}
    (hcone : SmoothCovariance.StrictCone (G x) (T x)) (hx : 0 < x) (i : Fin 2) :
    0 < primaryAmplitude σ κ G T x i :=
  Real.sqrt_pos.mpr (inverseCoefficients_pos hcone hx i)

/-- The inverse still reconstructs its target at every real point, including
the zero half-line where the matrix itself is singular. -/
theorem inverse_reconstruct (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) {x : ℝ} (hG : (G x).det ≠ 0) :
    (edgeMatrix κ G x).mulVec (inverseCoefficients σ κ G T x) = edgeTarget σ T x := by
  by_cases hx : x ≤ 0
  · rw [inverseCoefficients_of_nonpos σ κ G T hx, Matrix.mulVec_zero]
    ext i
    simp [edgeTarget, scaledTarget, FlatCutoff.edge_of_nonpos σ hx]
  · have hp : 0 < x := lt_of_not_ge hx
    unfold inverseCoefficients
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (edgeMatrix_det_ne_zero hG hp)),
      Matrix.one_mulVec]

theorem primary_reconstruct {σ : ℝ} {κ : Vec2}
    {G : ℝ → Mat2} {T : ℝ → Vec2} {x : ℝ}
    (hcone : SmoothCovariance.StrictCone (G x) (T x)) :
    (edgeMatrix κ G x).mulVec (fun i => primaryAmplitude σ κ G T x i ^ 2) =
      edgeTarget σ T x := by
  have hy : ∀ i, 0 ≤ inverseCoefficients σ κ G T x i := by
    intro i
    by_cases hx : x ≤ 0
    · simp [inverseCoefficients_of_nonpos σ κ G T hx]
    · exact le_of_lt (inverseCoefficients_pos hcone (lt_of_not_ge hx) i)
  have hs : (fun i => primaryAmplitude σ κ G T x i ^ 2) =
      inverseCoefficients σ κ G T x := by
    funext i
    exact Real.sq_sqrt (hy i)
  rw [hs]
  exact inverse_reconstruct σ κ G T hcone.det_ne_zero

/-- Exact two-sided cross covariance of the primary and signed increment. -/
theorem signed_cross_reconstruct {σ τ : ℝ} {κ : Vec2}
    {G : ℝ → Mat2} {T R : ℝ → Vec2} {x : ℝ}
    (hcone : SmoothCovariance.StrictCone (G x) (T x)) :
    (edgeMatrix κ G x).mulVec
        (fun i => 2 * primaryAmplitude σ κ G T x i * signedAmplitude σ τ κ G T R x i) =
      edgeTarget τ R x := by
  have hcross :
      (fun i => 2 * primaryAmplitude σ κ G T x i * signedAmplitude σ τ κ G T R x i) =
        inverseCoefficients τ κ G R x := by
    funext i
    by_cases hx : x ≤ 0
    · simp [primaryAmplitude_of_nonpos σ κ G T hx,
        inverseCoefficients_of_nonpos τ κ G R hx]
    · have ha : primaryAmplitude σ κ G T x i ≠ 0 :=
        ne_of_gt (primaryAmplitude_pos hcone (lt_of_not_ge hx) i)
      unfold signedAmplitude
      field_simp
  rw [hcross]
  exact inverse_reconstruct τ κ G R hcone.det_ne_zero

section Smooth

variable {s : Set ℝ} {σ τ : ℝ} {κ : Vec2}
variable {G : ℝ → Mat2} {T R : ℝ → Vec2}

theorem edgeMatrix_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hκ : ∀ i, 0 < κ i) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => edgeMatrix κ G x i j) s :=
  (FlatCutoff.edge_contDiff (hκ j) (n := ⊤)).contDiffOn.mul (hG i j)

theorem edgeTarget_contDiffOn
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hσ : 0 < σ) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => edgeTarget σ T x i) s :=
  (FlatCutoff.edge_contDiff hσ (n := ⊤)).contDiffOn.mul (hT i)

/-- Smooth inverse coefficients at the edge, proved by the surviving
exponential factor even though the actual matrix degenerates there. -/
theorem inverseCoefficients_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hdet : ∀ x ∈ s, (G x).det ≠ 0)
    (hgap : ∀ i, κ i < σ) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => inverseCoefficients σ κ G T x i) s := by
  apply ((FlatCutoff.edge_contDiff (sub_pos.mpr (hgap i)) (n := ⊤)).contDiffOn.mul
    (SmoothCovariance.contDiffOn_weights hG hT hdet i)).congr
  intro x hx
  exact inverseCoefficients_factor σ κ G T (hdet x hx) i

theorem primaryAmplitude_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, κ i < σ) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => primaryAmplitude σ κ G T x i) s := by
  have hp : 0 < (σ - κ i) / 2 := by linarith [hgap i]
  apply ((FlatCutoff.edge_contDiff hp (n := ⊤)).contDiffOn.mul
    (SmoothCovariance.contDiffOn_amplitudes hG hT hcone i)).congr
  intro x hx
  exact primaryAmplitude_factor σ κ G T (hcone x hx).det_ne_zero i

/-- Every fixed inverse-power loss is absorbed by the concrete primary
exponential, including at zero. -/
theorem primaryAmplitude_div_pow_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, κ i < σ) (i : Fin 2) (loss : ℕ) :
    ContDiffOn ℝ ∞ (fun x => primaryAmplitude σ κ G T x i / x ^ loss) s := by
  have hp : 0 < (σ - κ i) / 2 := by linarith [hgap i]
  apply ((FlatCutoff.edge_div_pow_contDiff hp loss (n := ⊤)).contDiffOn.mul
    (SmoothCovariance.contDiffOn_amplitudes hG hT hcone i)).congr
  intro x hx
  rw [primaryAmplitude_factor σ κ G T (hcone x hx).det_ne_zero i]
  ring

/-- The normalized signed quotient is smooth because its denominator is
proved strictly positive from the explicit normalized cone. -/
theorem signed_normal_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun x => R x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x)) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => SmoothCovariance.weights (G x) (R x) i /
      (2 * SmoothCovariance.amplitudes (G x) (T x) i)) s := by
  apply (SmoothCovariance.contDiffOn_weights hG hR
    (fun x hx => (hcone x hx).det_ne_zero) i).div
      (contDiffOn_const.mul (SmoothCovariance.contDiffOn_amplitudes hG hT hcone i))
  intro x hx
  exact mul_ne_zero (by norm_num) (ne_of_gt ((hcone x hx).amplitudes_pos i))

theorem signedAmplitude_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun x => R x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, (σ + κ i) / 2 < τ) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => signedAmplitude σ τ κ G T R x i) s := by
  apply ((FlatCutoff.edge_contDiff (sub_pos.mpr (hgap i)) (n := ⊤)).contDiffOn.mul
    (signed_normal_contDiffOn hG hT hR hcone i)).congr
  intro x hx
  exact signedAmplitude_factor σ τ κ G T R (hcone x hx).det_ne_zero i

theorem signedAmplitude_div_pow_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun x => R x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, (σ + κ i) / 2 < τ) (i : Fin 2) (loss : ℕ) :
    ContDiffOn ℝ ∞ (fun x => signedAmplitude σ τ κ G T R x i / x ^ loss) s := by
  apply ((FlatCutoff.edge_div_pow_contDiff (sub_pos.mpr (hgap i)) loss (n := ⊤)).contDiffOn.mul
    (signed_normal_contDiffOn hG hT hR hcone i)).congr
  intro x hx
  rw [signedAmplitude_factor σ τ κ G T R (hcone x hx).det_ne_zero i]
  ring

/-- An actual signed-stress numerator with an inverse-power loss still gives
a smooth signed amplitude. Smoothness of the singular quotient is a result. -/
theorem signed_inverse_power_target_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun x => R x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, (σ + κ i) / 2 < τ) (i : Fin 2) (loss : ℕ) :
    ContDiffOn ℝ ∞ (fun x => signedAmplitude σ τ κ G T
      (fun y j => (y ^ loss)⁻¹ * R y j) x i) s := by
  apply (signedAmplitude_div_pow_contDiffOn hG hT hR hcone hgap i loss).congr
  intro x hx
  rw [signedAmplitude_target_factor]
  simp only [div_eq_mul_inv]
  ring

/-- When a fundamental column factor is `edge λᵢ` and covariance therefore
carries its square, the concrete condition is exactly `λᵢ < σ / 2`. A signed
stress with the same target envelope retains the same flat exponent. -/
theorem squared_factors_smooth {lam : Vec2}
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun x => R x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, lam i < σ / 2) (i : Fin 2) (loss : ℕ) :
    ContDiffOn ℝ ∞ (fun x => primaryAmplitude σ (fun j => 2 * lam j) G T x i / x ^ loss) s ∧
    ContDiffOn ℝ ∞ (fun x => signedAmplitude σ σ (fun j => 2 * lam j) G T R x i / x ^ loss) s := by
  constructor
  · exact primaryAmplitude_div_pow_contDiffOn hG hT hcone
      (fun j => by linarith [hgap j]) i loss
  · exact signedAmplitude_div_pow_contDiffOn hG hT hR hcone
      (fun j => by linarith [hgap j]) i loss

/-- The requested stricter half-exponent condition also suffices when the
exponential appears directly in a covariance column, without a square. -/
theorem direct_half_factors_smooth
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun x => R x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x))
    (hσ : 0 < σ) (hgap : ∀ i, κ i < σ / 2) (i : Fin 2) (loss : ℕ) :
    ContDiffOn ℝ ∞ (fun x => primaryAmplitude σ κ G T x i / x ^ loss) s ∧
    ContDiffOn ℝ ∞ (fun x => signedAmplitude σ σ κ G T R x i / x ^ loss) s := by
  constructor
  · exact primaryAmplitude_div_pow_contDiffOn hG hT hcone
      (fun j => by linarith [hgap j]) i loss
  · exact signedAmplitude_div_pow_contDiffOn hG hT hR hcone
      (fun j => by linarith [hgap j]) i loss

end Smooth

/-- Concrete compact-family lower bounds with the vanishing factors left
explicit. In particular the primary square-root denominator is controlled. -/
theorem compact_weighted_lower_bounds {K : Set ℝ} (hK : IsCompact K)
    {σ : ℝ} {κ : Vec2} {G : ℝ → Mat2} {T : ℝ → Vec2}
    (hG : ∀ i j, ContinuousOn (fun x => G x i j) K)
    (hT : ∀ i, ContinuousOn (fun x => T x i) K)
    (hcone : ∀ x ∈ K, SmoothCovariance.StrictCone (G x) (T x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ i,
      δ * edge (σ - κ i) x ≤ inverseCoefficients σ κ G T x i ∧
      δ * edge ((σ - κ i) / 2) x ≤ primaryAmplitude σ κ G T x i := by
  obtain ⟨δ, hδ, hbound⟩ := SmoothCovariance.compact_uniform_amplitudes hK hG hT hcone
  refine ⟨δ, hδ, ?_⟩
  intro x hx i
  rw [inverseCoefficients_factor σ κ G T (hcone x hx).det_ne_zero i,
    primaryAmplitude_factor σ κ G T (hcone x hx).det_ne_zero i]
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left ((hbound x hx).2 i).1
      (FlatCutoff.edge_nonneg (σ - κ i) x)
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left ((hbound x hx).2 i).2
      (FlatCutoff.edge_nonneg ((σ - κ i) / 2) x)

/-- A smooth function that is zero on the nonpositive half-line has every
derivative zero at the joining point. -/
theorem iteratedDeriv_zero_of_nonpos_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hzero : ∀ x ≤ 0, f x = 0) (n : ℕ) :
    iteratedDeriv n f 0 = 0 := by
  have hz : iteratedDeriv n (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
    induction n with
    | zero => rw [iteratedDeriv_zero]
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact deriv_const x 0
  have heq : EqOn f (fun _ : ℝ => (0 : ℝ)) (Iio 0) :=
    fun x hx => hzero x hx.le
  have hd := heq.iteratedDeriv_of_isOpen isOpen_Iio n
  rw [hz] at hd
  have hc : Continuous (iteratedDeriv n f) := hf.continuous_iteratedDeriv n
    (WithTop.coe_le_coe.mpr (le_top : (n : ℕ∞) ≤ ⊤))
  have hcl := hd.closure hc continuous_const
  apply hcl
  simp

section GlobalFlatness

variable {σ τ : ℝ} {κ : Vec2} {G : ℝ → Mat2} {T R : ℝ → Vec2}

theorem primaryAmplitude_div_pow_contDiff
    (hG : ∀ i j, ContDiff ℝ ∞ (fun x => G x i j))
    (hT : ∀ i, ContDiff ℝ ∞ (fun x => T x i))
    (hcone : ∀ x, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, κ i < σ) (i : Fin 2) (loss : ℕ) :
    ContDiff ℝ ∞ (fun x => primaryAmplitude σ κ G T x i / x ^ loss) :=
  contDiffOn_univ.mp (primaryAmplitude_div_pow_contDiffOn
    (fun i j => (hG i j).contDiffOn) (fun i => (hT i).contDiffOn)
    (fun x _ => hcone x) hgap i loss)

theorem signedAmplitude_div_pow_contDiff
    (hG : ∀ i j, ContDiff ℝ ∞ (fun x => G x i j))
    (hT : ∀ i, ContDiff ℝ ∞ (fun x => T x i))
    (hR : ∀ i, ContDiff ℝ ∞ (fun x => R x i))
    (hcone : ∀ x, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, (σ + κ i) / 2 < τ) (i : Fin 2) (loss : ℕ) :
    ContDiff ℝ ∞ (fun x => signedAmplitude σ τ κ G T R x i / x ^ loss) :=
  contDiffOn_univ.mp (signedAmplitude_div_pow_contDiffOn
    (fun i j => (hG i j).contDiffOn) (fun i => (hT i).contDiffOn)
    (fun i => (hR i).contDiffOn) (fun x _ => hcone x) hgap i loss)

/-- Actual all-order flatness of the primary, also after every fixed
inverse-power loss, obtained from the proved smooth zero extension. -/
theorem primary_weighted_derivatives_zero
    (hG : ∀ i j, ContDiff ℝ ∞ (fun x => G x i j))
    (hT : ∀ i, ContDiff ℝ ∞ (fun x => T x i))
    (hcone : ∀ x, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, κ i < σ) (i : Fin 2) (loss n : ℕ) :
    iteratedDeriv n (fun x => primaryAmplitude σ κ G T x i / x ^ loss) 0 = 0 := by
  apply iteratedDeriv_zero_of_nonpos_zero
    (primaryAmplitude_div_pow_contDiff hG hT hcone hgap i loss)
  intro x hx
  simp [primaryAmplitude_of_nonpos σ κ G T hx i]

theorem signed_weighted_derivatives_zero
    (hG : ∀ i j, ContDiff ℝ ∞ (fun x => G x i j))
    (hT : ∀ i, ContDiff ℝ ∞ (fun x => T x i))
    (hR : ∀ i, ContDiff ℝ ∞ (fun x => R x i))
    (hcone : ∀ x, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, (σ + κ i) / 2 < τ) (i : Fin 2) (loss n : ℕ) :
    iteratedDeriv n (fun x => signedAmplitude σ τ κ G T R x i / x ^ loss) 0 = 0 := by
  apply iteratedDeriv_zero_of_nonpos_zero
    (signedAmplitude_div_pow_contDiff hG hT hR hcone hgap i loss)
  intro x hx
  simp [signedAmplitude_of_nonpos σ τ κ G T R hx i]

end GlobalFlatness

section ParameterFamilies

variable {E : Type*}

/-- Evaluation of the actual inverse amplitude at a smooth signed edge
coordinate, with independent smooth parameters in the normalized data. -/
def parameterPrimary (σ : ℝ) (κ : Vec2) (d : E → ℝ)
    (G : E → Mat2) (T : E → Vec2) (z : E) : Vec2 :=
  primaryAmplitude σ κ (fun _ => G z) (fun _ => T z) (d z)

/-- Parameter signed, given by `signedAmplitude σ τ κ (fun _ => G z) (fun _ => T z) (fun _ => R
z) (d z)`. -/
def parameterSigned (σ τ : ℝ) (κ : Vec2) (d : E → ℝ)
    (G : E → Mat2) (T R : E → Vec2) (z : E) : Vec2 :=
  signedAmplitude σ τ κ (fun _ => G z) (fun _ => T z) (fun _ => R z) (d z)

theorem parameterPrimary_of_nonpos (σ : ℝ) (κ : Vec2) (d : E → ℝ)
    (G : E → Mat2) (T : E → Vec2) {z : E} (hz : d z ≤ 0) (i : Fin 2) :
    parameterPrimary σ κ d G T z i = 0 :=
  primaryAmplitude_of_nonpos σ κ (fun _ => G z) (fun _ => T z) hz i

theorem parameterSigned_of_nonpos (σ τ : ℝ) (κ : Vec2) (d : E → ℝ)
    (G : E → Mat2) (T R : E → Vec2) {z : E} (hz : d z ≤ 0) (i : Fin 2) :
    parameterSigned σ τ κ d G T R z i = 0 :=
  signedAmplitude_of_nonpos σ τ κ (fun _ => G z) (fun _ => T z) (fun _ => R z) hz i

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Joint smoothness in the edge coordinate and all additional parameters,
after any fixed inverse power of the edge coordinate. -/
theorem parameterPrimary_div_pow_contDiffOn
    {s : Set E} {σ : ℝ} {κ : Vec2} {d : E → ℝ}
    {G : E → Mat2} {T : E → Vec2}
    (hd : ContDiffOn ℝ ∞ d s)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z => G z i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun z => T z i) s)
    (hcone : ∀ z ∈ s, SmoothCovariance.StrictCone (G z) (T z))
    (hgap : ∀ i, κ i < σ) (i : Fin 2) (loss : ℕ) :
    ContDiffOn ℝ ∞ (fun z => parameterPrimary σ κ d G T z i / d z ^ loss) s := by
  have hp : 0 < (σ - κ i) / 2 := by linarith [hgap i]
  apply (((FlatCutoff.edge_div_pow_contDiff hp loss (n := ⊤)).comp_contDiffOn hd).mul
    (SmoothCovariance.contDiffOn_amplitudes hG hT hcone i)).congr
  intro z hz
  unfold parameterPrimary
  rw [primaryAmplitude_factor σ κ (fun _ => G z) (fun _ => T z)
    (hcone z hz).det_ne_zero i]
  dsimp only [Function.comp_def]
  ring

theorem parameterSigned_div_pow_contDiffOn
    {s : Set E} {σ τ : ℝ} {κ : Vec2} {d : E → ℝ}
    {G : E → Mat2} {T R : E → Vec2}
    (hd : ContDiffOn ℝ ∞ d s)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z => G z i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun z => T z i) s)
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun z => R z i) s)
    (hcone : ∀ z ∈ s, SmoothCovariance.StrictCone (G z) (T z))
    (hgap : ∀ i, (σ + κ i) / 2 < τ) (i : Fin 2) (loss : ℕ) :
    ContDiffOn ℝ ∞ (fun z => parameterSigned σ τ κ d G T R z i / d z ^ loss) s := by
  have hn : ContDiffOn ℝ ∞ (fun z => SmoothCovariance.weights (G z) (R z) i /
      (2 * SmoothCovariance.amplitudes (G z) (T z) i)) s := by
    apply (SmoothCovariance.contDiffOn_weights hG hR
      (fun z hz => (hcone z hz).det_ne_zero) i).div
        (contDiffOn_const.mul (SmoothCovariance.contDiffOn_amplitudes hG hT hcone i))
    intro z hz
    exact mul_ne_zero (by norm_num) (ne_of_gt ((hcone z hz).amplitudes_pos i))
  apply (((FlatCutoff.edge_div_pow_contDiff (sub_pos.mpr (hgap i)) loss
    (n := ⊤)).comp_contDiffOn hd).mul hn).congr
  intro z hz
  unfold parameterSigned
  rw [signedAmplitude_factor σ τ κ (fun _ => G z) (fun _ => T z) (fun _ => R z)
    (hcone z hz).det_ne_zero i]
  dsimp only [Function.comp_def]
  ring

end ParameterFamilies

end NavierStokes.FlatCovariance
