/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TensorNorm

/-! Ordered spatial derivatives and the actual source seminorm. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Ordered spatial differentiation of a scalar on the actual Vec carrier. -/
def amnrSpaceWord : List (Fin 2) → (Vec 2 → ℝ) → Vec 2 → ℝ
  | [], f => f
  | i :: α, f => fun x => fderiv ℝ (amnrSpaceWord α f) x (basisVec i)

/-- Coordinate tuple corresponding to the ordered spatial word. -/
def amnrSpatialIndices : (α : List (Fin 2)) → Fin α.length → Fin 2
  | [], j => Fin.elim0 j
  | i :: α, j => Fin.cons (α := fun _ : Fin (α.length + 1) => Fin 2) i (amnrSpatialIndices α) j

/-- The exact tuple of spatial directions, retaining the word order. -/
def amnrSpatialDirections : (α : List (Fin 2)) → Fin α.length → Vec 2
  | [], j => Fin.elim0 j
  | i :: α, j => Fin.cons (α := fun _ : Fin (α.length + 1) => Vec 2) (basisVec i)
      (amnrSpatialDirections α) j

theorem amnrSpatialDirections_eq (α : List (Fin 2)) :
    amnrSpatialDirections α = fun j => basisVec (amnrSpatialIndices α j) := by
  induction α with
  | nil => funext j; exact Fin.elim0 j
  | cons i α ih =>
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · simpa only [amnrSpatialDirections, amnrSpatialIndices, Fin.cons_succ] using congrFun ih k

/-- The ordered spatial derivatives are the actual iterated Frechet derivative
on the coordinate tuple, rather than a separate derivative carrier. -/
theorem amnrSpaceWord_eq_iteratedFDeriv {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α : List (Fin 2)) :
    amnrSpaceWord α f = fun x => iteratedFDeriv ℝ α.length f x (amnrSpatialDirections α) := by
  induction α with
  | nil => rfl
  | cons i α ih =>
    funext x
    simp only [amnrSpaceWord]
    rw [ih]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ α.length f) x :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top α.length) x
    have hh := hd.iteratedFDeriv_succ_apply_left'
      (m := Fin.cons (α := fun _ : Fin (α.length + 1) => Vec 2) (basisVec i)
          (amnrSpatialDirections α))
    simpa only [List.length_cons, amnrSpatialDirections, Fin.cons_zero, Fin.tail_cons] using hh.symm

/-- Source seminorm control applies to every ordered spatial derivative with
its exact factorial factor. -/
theorem amnrSpaceWord_norm_le_of_barNorm {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α : List (Fin 2)) {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B)
    (hb : AVenhance.barNorm α.length R f ≤ ENNReal.ofReal B) (x : Vec 2) :
    ‖amnrSpaceWord α f x‖ ≤
      B * (α.length.factorial : ℝ) * R ^ α.length / ((α.length : ℝ) + 1) ^ 2 := by
  rw [amnrSpaceWord_eq_iteratedFDeriv hf α, amnrSpatialDirections_eq]
  exact amnr_partial_norm_le_of_barNorm f α.length (hf.of_le (by simp)) hR hB hb x _

/-- The spatial part of the mixed calculus is exactly the ordered derivative
of the time slice. No quantitative assumption enters this bridge. -/
theorem amnrWord_spatial_slice {f : AmnrSpace → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (b : AmnrSpace → Vec 2) (α : List (Fin 2)) :
    amnrWord b (α.map some) f =
      fun z => amnrSpaceWord α (fun y => f (z.1, y)) z.2 := by
  rw [amnrWord_spatial_independent b (fun _ => (0 : Vec 2)) α f]
  induction α with
  | nil => rfl
  | cons i α ih =>
    funext z
    have hg := amnrWord_contDiffOn_infty isOpen_univ
      (contDiffOn_const : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : AmnrSpace => (0 : Vec 2)) Set.univ)
      hf.contDiffOn (α.map some)
    have hd := (hg.contDiffAt (isOpen_univ.mem_nhds (Set.mem_univ z))).differentiableAt (by simp)
    simp only [List.map_cons, amnrWord]
    rw [amnrOp_space hd i]
    have heq : (fun y => amnrWord (fun _ => (0 : Vec 2)) (α.map some) f (z.1, y)) =
        amnrSpaceWord α (fun y => f (z.1, y)) := by
      funext y
      exact congrFun ih (z.1, y)
    rw [heq]
    rfl

/-- Concatenating spatial words composes the actual derivative operators. -/
theorem amnrSpaceWord_append (α η : List (Fin 2)) (f : Vec 2 → ℝ) :
    amnrSpaceWord (α ++ η) f = amnrSpaceWord α (amnrSpaceWord η f) := by
  induction α with
  | nil => rfl
  | cons i α ih => simp only [List.cons_append, amnrSpaceWord, ih]

/-- Scalar multiplication commutes with all spatial derivatives, including
at points where the total Frechet derivative uses its default value. -/
theorem amnrSpaceWord_const_smul (c : ℝ) (α : List (Fin 2)) (f : Vec 2 → ℝ) :
    amnrSpaceWord α (c • f) = c • amnrSpaceWord α f := by
  induction α with
  | nil => rfl
  | cons i α ih =>
    simp only [amnrSpaceWord, ih]
    funext x
    rw [congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := amnrSpaceWord α f) c) x]
    rfl

/-- The source velocity-gradient slice has precisely the two spatial
stream derivatives and the rotation sign encoded by sigmaMat. -/
theorem amnrVelocityGradient_stream_zero (φ : ℝ → Vec 2 → ℝ) (p : Fin 2) (t : ℝ) :
    (fun x => amnrVelocityGradient (fun z => AVenhance.streamVel φ z.1 z.2) 0 p (t, x)) =
      (-1 : ℝ) • amnrSpaceWord [p, 1] (φ t) := by
  have heq : (fun y => AVenhance.streamVel φ t y 0) =
      (-1 : ℝ) • (fun y => AVenhance.spaceGrad (φ t) y 1) := by
    funext y
    simp [AVenhance.streamVel, AVenhance.sigmaMat, dotProduct, Fin.sum_univ_two]
  funext x
  unfold amnrVelocityGradient
  rw [heq]
  unfold AVenhance.spaceGrad
  rw [congrFun (fderiv_const_smul_field (𝕜 := ℝ)
    (f := fun y => fderiv ℝ (φ t) y (basisVec 1)) (-1 : ℝ)) x]
  rfl

theorem amnrVelocityGradient_stream_one (φ : ℝ → Vec 2 → ℝ) (p : Fin 2) (t : ℝ) :
    (fun x => amnrVelocityGradient (fun z => AVenhance.streamVel φ z.1 z.2) 1 p (t, x)) =
      amnrSpaceWord [p, 0] (φ t) := by
  have heq : (fun y => AVenhance.streamVel φ t y 1) =
      (fun y => AVenhance.spaceGrad (φ t) y 0) := by
    funext y
    simp [AVenhance.streamVel, AVenhance.sigmaMat, dotProduct, Fin.sum_univ_two]
  funext x
  unfold amnrVelocityGradient
  rw [heq]
  rfl

end AVenhance.Infra.Section4
