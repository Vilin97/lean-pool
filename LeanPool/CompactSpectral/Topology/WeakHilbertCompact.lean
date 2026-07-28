/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Weak compactness of Hilbert closed balls

If `E` is a (real or complex) Hilbert space, then the norm-closed ball is compact in the weak
topology on `E`.

This is a “Riesz + Banach–Alaoglu” bridge:
- Use the Riesz representation theorem (`InnerProductSpace.toDual`) to identify `E` with its
  continuous dual.
- Transfer Banach–Alaoglu compactness (`WeakDual.isCompact_closedBall`) to `WeakSpace 𝕜 E`.

This lemma is a key building block for developing compact/self-adjoint spectral theory in a
Hilbert setting while keeping `packages/mathlib_extensions/` mathlib-only.
-/

namespace CompactSpectral

open scoped Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Norm on `WeakSpace 𝕜 E` inherited from `E`. Since `WeakSpace 𝕜 E := E`,
this lets us write `‖x‖` for `x : WeakSpace 𝕜 E` without explicit coercion. -/
noncomputable scoped instance instNormWeakSpace :
    Norm (WeakSpace 𝕜 E) := ⟨@norm E _⟩

/-! ### Weak ↔ weak-star maps via Riesz -/

/-- The Riesz map `E → E*` viewed as a function from the weak topology on `E`
(`WeakSpace 𝕜 E`) to the weak-star topology on the dual (`WeakDual 𝕜 E`). -/
noncomputable def weakToWeakDual : WeakSpace 𝕜 E → WeakDual 𝕜 E :=
  fun x => StrongDual.toWeakDual ((InnerProductSpace.toDual 𝕜 E) (x : E))

/-- The inverse Riesz map `E* → E` viewed as a function from the weak-star dual (`WeakDual 𝕜 E`)
to the weak topology on `E` (`WeakSpace 𝕜 E`). -/
noncomputable def weakDualToWeak : WeakDual 𝕜 E → WeakSpace 𝕜 E :=
  fun f => (InnerProductSpace.toDual 𝕜 E).symm (WeakDual.toStrongDual f)

lemma continuous_weakToWeakDual : Continuous (weakToWeakDual (𝕜 := 𝕜) (E := E)) := by
  refine WeakDual.continuous_of_continuous_eval (𝕜 := 𝕜) (E := E)
    (g := weakToWeakDual (𝕜 := 𝕜) (E := E)) ?_
  intro y
  have h_eval : Continuous (fun x : WeakSpace 𝕜 E => (InnerProductSpace.toDual 𝕜 E y) x) := by
    have h := WeakBilin.eval_continuous (B := (topDualPairing 𝕜 E).flip)
      (y := (InnerProductSpace.toDual 𝕜 E y))
    exact h
  have h_conj : Continuous (fun z : 𝕜 => star z) := by
    simpa using (continuous_star : Continuous fun z : 𝕜 => star z)
  have h : Continuous (fun x : WeakSpace 𝕜 E => star ((InnerProductSpace.toDual 𝕜 E y) x)) :=
    h_conj.comp h_eval
  have h_eq :
      (fun x : WeakSpace 𝕜 E => (weakToWeakDual (𝕜 := 𝕜) (E := E) x) y) =
        fun x : WeakSpace 𝕜 E => star ((InnerProductSpace.toDual 𝕜 E y) x) := by
    funext x
    exact (inner_conj_symm (𝕜 := 𝕜) (E := E) x y).symm
  simpa [h_eq] using h

private lemma eval_weakDualToWeak (l : E →L[𝕜] 𝕜) (f : WeakDual 𝕜 E) :
    l (weakDualToWeak (𝕜 := 𝕜) (E := E) f) =
      (starRingEnd 𝕜)
        (f ((InnerProductSpace.toDual 𝕜 E).symm l)) := by
  simp only [weakDualToWeak]
  have hL :
      l ((InnerProductSpace.toDual 𝕜 E).symm f) =
        inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm l)
          ((InnerProductSpace.toDual 𝕜 E).symm f) := by
    simp_all
  have hR :
      f ((InnerProductSpace.toDual 𝕜 E).symm l) =
        inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm f)
          ((InnerProductSpace.toDual 𝕜 E).symm l) := by
    exact (InnerProductSpace.toDual_symm_apply (𝕜 := 𝕜) (E := E)
      (x := (InnerProductSpace.toDual 𝕜 E).symm l)
      (y := f)).symm
  have hInner :
      inner 𝕜
        ((InnerProductSpace.toDual 𝕜 E).symm l)
        ((InnerProductSpace.toDual 𝕜 E).symm f) =
        star (inner 𝕜
          ((InnerProductSpace.toDual 𝕜 E).symm f)
          ((InnerProductSpace.toDual 𝕜 E).symm l)) :=
    (inner_conj_symm (𝕜 := 𝕜)
      ((InnerProductSpace.toDual 𝕜 E).symm l)
      ((InnerProductSpace.toDual 𝕜 E).symm f)).symm
  calc
    l ((InnerProductSpace.toDual 𝕜 E).symm f)
        = inner 𝕜
            ((InnerProductSpace.toDual 𝕜 E).symm l)
            ((InnerProductSpace.toDual 𝕜 E).symm f)
            := hL
    _ = star (inner 𝕜
          ((InnerProductSpace.toDual 𝕜 E).symm f)
          ((InnerProductSpace.toDual 𝕜 E).symm l))
          := hInner
    _ = star (f ((InnerProductSpace.toDual 𝕜 E).symm l)) := by
          exact congrArg star hR.symm
    _ = (starRingEnd 𝕜) (f ((InnerProductSpace.toDual 𝕜 E).symm l)) := by
          exact (starRingEnd_apply (R := 𝕜) (f ((InnerProductSpace.toDual 𝕜 E).symm l))).symm

lemma continuous_weakDualToWeak : Continuous (weakDualToWeak (𝕜 := 𝕜) (E := E)) := by
  refine WeakBilin.continuous_of_continuous_eval (B := (topDualPairing 𝕜 E).flip)
    (g := weakDualToWeak (𝕜 := 𝕜) (E := E)) ?_
  intro l
  have h_eval :
      Continuous (fun f : WeakDual 𝕜 E => f ((InnerProductSpace.toDual 𝕜 E).symm l)) := by
    simpa using
      (WeakDual.eval_continuous (𝕜 := 𝕜) (E := E) ((InnerProductSpace.toDual 𝕜 E).symm l))
  have h_conj : Continuous (fun z : 𝕜 => (starRingEnd 𝕜) z) := by
    have h : (fun z : 𝕜 => (starRingEnd 𝕜) z) = fun z : 𝕜 => star z := by
      simp_all
    rw [h]
    exact (continuous_star : Continuous fun z : 𝕜 => star z)
  have h :
      Continuous
        (fun f : WeakDual 𝕜 E => (starRingEnd 𝕜) (f ((InnerProductSpace.toDual 𝕜 E).symm l))) :=
    h_conj.comp h_eval
  exact h.congr fun f => (eval_weakDualToWeak (𝕜 := 𝕜) (E := E) l f).symm

/-! ### Closed balls -/

/-- The norm-closed ball, viewed as a subset of `WeakSpace 𝕜 E`. -/
noncomputable def weakClosedBall (r : ℝ) : Set (WeakSpace 𝕜 E) :=
  Metric.closedBall (α := E) (0 : E) r

/-- The (weak-*) closed ball in the dual, as a subset of `WeakDual 𝕜 E`. -/
noncomputable def weakDualClosedBall (r : ℝ) : Set (WeakDual 𝕜 E) :=
  (fun f : WeakDual 𝕜 E => WeakDual.toStrongDual f) ⁻¹'
    Metric.closedBall (α := StrongDual 𝕜 E) (0 : StrongDual 𝕜 E) r

private lemma weakDualToWeak_left_inv :
    Function.LeftInverse (weakDualToWeak (𝕜 := 𝕜) (E := E))
      (weakToWeakDual (𝕜 := 𝕜) (E := E)) := by
  intro x
  unfold weakDualToWeak weakToWeakDual
  exact (InnerProductSpace.toDual 𝕜 E).symm_apply_apply (x : E)

private lemma weakDualToWeak_image_weakDualClosedBall (r : ℝ) :
    weakDualToWeak (𝕜 := 𝕜) (E := E) ''
      weakDualClosedBall (𝕜 := 𝕜) (E := E) r =
      weakClosedBall (𝕜 := 𝕜) (E := E) r := by
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hf_norm : ‖WeakDual.toStrongDual f‖ ≤ r :=
      (mem_closedBall_zero_iff
        (a := WeakDual.toStrongDual f) (r := r)).1 hf
    have hx_norm :
        ‖(InnerProductSpace.toDual 𝕜 E).symm
          (WeakDual.toStrongDual f)‖ ≤ r := by
      simp_all
    let y : E := weakDualToWeak (𝕜 := 𝕜) (E := E) f
    change y ∈ Metric.closedBall (0 : E) r
    exact mem_closedBall_zero_iff.2
      (show ‖y‖ ≤ r by
        simp only [y, weakDualToWeak]; exact hx_norm)
  · intro hx
    refine ⟨weakToWeakDual (𝕜 := 𝕜) (E := E) x, ?_, by
      simpa using
        weakDualToWeak_left_inv (𝕜 := 𝕜) (E := E) x⟩
    let y : E := x
    have hy : y ∈ Metric.closedBall (0 : E) r := hx
    have hy_norm : ‖y‖ ≤ r := mem_closedBall_zero_iff.1 hy
    have h_toDual_norm :
        ‖(InnerProductSpace.toDual 𝕜 E) y‖ ≤ r := by
      rwa [(InnerProductSpace.toDual 𝕜 E).norm_map]
    change weakToWeakDual (𝕜 := 𝕜) (E := E) x ∈
      weakDualClosedBall r
    unfold weakDualClosedBall weakToWeakDual
    simp only [Set.mem_preimage]
    exact mem_closedBall_zero_iff.2 h_toDual_norm

/-- In a Hilbert space `E`, the norm-closed ball is compact for the weak topology. -/
theorem isCompact_weakClosedBall (r : ℝ) : IsCompact (weakClosedBall (𝕜 := 𝕜) (E := E) r) := by
  have hK : IsCompact (weakDualClosedBall (𝕜 := 𝕜) (E := E) r) := by
    simpa [weakDualClosedBall] using
      (WeakDual.isCompact_closedBall (𝕜 := 𝕜) (E := E) (x' := (0 : StrongDual 𝕜 E)) r)
  have himage :
      IsCompact (weakDualToWeak (𝕜 := 𝕜) (E := E) '' weakDualClosedBall (𝕜 := 𝕜) (E := E) r) :=
    hK.image (continuous_weakDualToWeak (𝕜 := 𝕜) (E := E))
  simpa [weakDualToWeak_image_weakDualClosedBall (𝕜 := 𝕜) (E := E) r] using himage

end CompactSpectral
