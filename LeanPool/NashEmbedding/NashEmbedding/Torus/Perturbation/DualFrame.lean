/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic
import LeanPool.NashEmbedding.NashEmbedding.Torus.Basic

/-!
# Dual frames

Given a finite family `e : ι → ℝⁿ → ℝᴺ` of smooth vector fields that is linearly
independent at every point, we construct a smooth *dual frame*
`d : ι → ℝⁿ → ℝᴺ` with `d i x ⬝ᵥ e j x = δᵢⱼ`, namely
`d i x = ∑ⱼ (G x)⁻¹ i j • e j x` where `G x = (e i x ⬝ᵥ e j x)` is the Gram matrix.
Linear independence makes `G x` invertible, and its inverse is smooth because
`G⁻¹ = det(G)⁻¹ • adjugate(G)` with `det`, `adjugate` polynomial in the entries.

In Theorem B (Günther's perturbation theorem) this is applied to the frame
`{∂ᵢu⁰} ∪ {∂ᵢ∂ⱼu⁰ : i ≤ j}` of a free embedding `u⁰`, producing the fields
`aᵢ, b_{pq}` with which the ansatz `v ⬝ ∂ᵢu⁰ = -Fᵢ(v)`, `v ⬝ ∂ᵢ∂ⱼu⁰ = ½(Uᵢⱼ(v) - hᵢⱼ)`
is solved pointwise. Periodicity of the dual frame is inherited pointwise.
-/

open scoped BigOperators ContDiff
open NashEmbedding.Sobolev Matrix

noncomputable section

namespace NashEmbedding

variable {n N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Smoothness of determinants and inverses, entrywise -/

/-- If every entry of a matrix-valued function is smooth, so is its determinant. -/
lemma det_contDiff {M : (Fin n → ℝ) → Matrix ι ι ℝ}
    (hM : ∀ i j, ContDiff ℝ ∞ (fun x => M x i j)) :
    ContDiff ℝ ∞ (fun x => (M x).det) := by
  simp only [det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM (σ i) i)

/-- If every entry of a matrix-valued function is smooth, so is every entry of its adjugate. -/
lemma adjugate_contDiff {M : (Fin n → ℝ) → Matrix ι ι ℝ}
    (hM : ∀ i j, ContDiff ℝ ∞ (fun x => M x i j)) (i j : ι) :
    ContDiff ℝ ∞ (fun x => (M x).adjugate i j) := by
  simp only [adjugate_apply]
  refine det_contDiff fun a b => ?_
  by_cases hab : a = j
  · subst hab; simp only [updateRow_self]; exact contDiff_const
  · simp only [updateRow_ne hab]; exact hM a b

/-- If every entry of a matrix-valued function is smooth and the determinant never vanishes,
every entry of the (nonsingular) inverse is smooth. -/
lemma inv_contDiff {M : (Fin n → ℝ) → Matrix ι ι ℝ}
    (hM : ∀ i j, ContDiff ℝ ∞ (fun x => M x i j)) (hdet : ∀ x, (M x).det ≠ 0) (i j : ι) :
    ContDiff ℝ ∞ (fun x => (M x)⁻¹ i j) := by
  have h : (fun x => (M x)⁻¹ i j) = fun x => ((M x).det)⁻¹ * (M x).adjugate i j := by
    funext x
    rw [inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  rw [h]
  exact ((det_contDiff hM).inv hdet).mul (adjugate_contDiff hM i j)

/-! ## Gram matrices -/

/-- The Gram matrix `G x = (e i x ⬝ᵥ e j x)ᵢⱼ` of a family of vector fields. -/
def gramMatrix (e : ι → (Fin n → ℝ) → (Fin N → ℝ)) (x : Fin n → ℝ) : Matrix ι ι ℝ :=
  fun i j => e i x ⬝ᵥ e j x

/-- A family of vector fields is *pointwise linearly independent* if the vectors
`e i x`, `i : ι`, are linearly independent for every `x`. -/
def IsPointwiseLinIndep (e : ι → (Fin n → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ x, LinearIndependent ℝ (fun i => e i x)

/-- The Gram determinant of a pointwise linearly independent family never vanishes. -/
lemma gramMatrix_det_ne_zero {e : ι → (Fin n → ℝ) → (Fin N → ℝ)}
    (he : IsPointwiseLinIndep e) (x : Fin n → ℝ) : (gramMatrix e x).det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
  -- kernel of `G.mulVec` is trivial: `c ⬝ᵥ G c = ‖∑ cᵢ eᵢ‖²`
  have hker : ∀ c : ι → ℝ, (gramMatrix e x).mulVec c = 0 → c = 0 := by
    intro c hc
    set w : Fin N → ℝ := ∑ i, c i • e i x with hw
    have hL : w ⬝ᵥ w = ∑ i, c i * ∑ j, (e i x ⬝ᵥ e j x) * c j := by
      simp only [hw, sum_dotProduct, smul_dotProduct, dotProduct_sum, dotProduct_smul,
        smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dotProduct_comm, mul_comm]
    have hR : c ⬝ᵥ (gramMatrix e x).mulVec c = ∑ i, c i * ∑ j, (e i x ⬝ᵥ e j x) * c j := by
      simp only [mulVec, dotProduct, gramMatrix]
    have hww : w ⬝ᵥ w = c ⬝ᵥ (gramMatrix e x).mulVec c := by rw [hL, hR]
    rw [hc, dotProduct_zero] at hww
    have hw0 : w = 0 := dotProduct_self_eq_zero.mp hww
    exact funext fun i => (Fintype.linearIndependent_iff.mp (he x)) c hw0 i
  intro c d hcd
  have : (gramMatrix e x).mulVec (c - d) = 0 := by rw [mulVec_sub, hcd, sub_self]
  exact sub_eq_zero.mp (hker _ this)

omit [Fintype ι] [DecidableEq ι] in
lemma gramMatrix_contDiff {e : ι → (Fin n → ℝ) → (Fin N → ℝ)}
    (he : ∀ i, ContDiff ℝ ∞ (e i)) (i j : ι) :
    ContDiff ℝ ∞ (fun x => gramMatrix e x i j) := by
  unfold gramMatrix dotProduct
  exact ContDiff.sum fun k _ =>
    ((contDiff_apply (𝕜 := ℝ) (E := ℝ) k).comp (he i)).mul
      ((contDiff_apply (𝕜 := ℝ) (E := ℝ) k).comp (he j))

omit [Fintype ι] [DecidableEq ι] in
lemma gramMatrix_periodic {e : ι → (Fin n → ℝ) → (Fin N → ℝ)}
    (he : ∀ i, IsPeriodic2Pi (e i)) (x : Fin n → ℝ) (k : Fin n → ℤ) :
    gramMatrix e (x + periodicShift n k) = gramMatrix e x := by
  funext i j
  simp only [gramMatrix, he i x k, he j x k]

/-! ## The dual frame -/

/-- The dual frame `d i x = ∑ⱼ (G x)⁻¹ i j • e j x`. -/
def dualFrame (e : ι → (Fin n → ℝ) → (Fin N → ℝ)) (i : ι) (x : Fin n → ℝ) : Fin N → ℝ :=
  ∑ j, (gramMatrix e x)⁻¹ i j • e j x

/-- Duality: `d i x ⬝ᵥ e j x = δᵢⱼ`. -/
theorem dualFrame_dotProduct {e : ι → (Fin n → ℝ) → (Fin N → ℝ)}
    (he : IsPointwiseLinIndep e) (i j : ι) (x : Fin n → ℝ) :
    dualFrame e i x ⬝ᵥ e j x = if i = j then 1 else 0 := by
  have hdet : IsUnit (gramMatrix e x).det := isUnit_iff_ne_zero.mpr (gramMatrix_det_ne_zero he x)
  have h1 : ((gramMatrix e x)⁻¹ * gramMatrix e x) i j = (1 : Matrix ι ι ℝ) i j := by
    rw [nonsing_inv_mul _ hdet]
  rw [one_apply, mul_apply] at h1
  rw [← h1, dualFrame, sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul, gramMatrix]

theorem dualFrame_contDiff {e : ι → (Fin n → ℝ) → (Fin N → ℝ)}
    (he : IsPointwiseLinIndep e) (hs : ∀ i, ContDiff ℝ ∞ (e i)) (i : ι) :
    ContDiff ℝ ∞ (dualFrame e i) := by
  unfold dualFrame
  exact ContDiff.sum fun j _ =>
    (inv_contDiff (gramMatrix_contDiff hs) (gramMatrix_det_ne_zero he) i j).smul (hs j)

theorem dualFrame_periodic {e : ι → (Fin n → ℝ) → (Fin N → ℝ)}
    (hp : ∀ i, IsPeriodic2Pi (e i)) (i : ι) : IsPeriodic2Pi (dualFrame e i) := by
  intro x k
  simp only [dualFrame, gramMatrix_periodic hp x k, hp _ x k]

theorem dualFrame_smoothPeriodic {e : ι → (Fin n → ℝ) → (Fin N → ℝ)}
    (he : IsPointwiseLinIndep e) (hsp : ∀ i, SmoothPeriodic (e i)) (i : ι) :
    SmoothPeriodic (dualFrame e i) :=
  ⟨dualFrame_contDiff he (fun i => (hsp i).smooth) i,
    dualFrame_periodic (fun i => (hsp i).periodic) i⟩

end NashEmbedding

end
