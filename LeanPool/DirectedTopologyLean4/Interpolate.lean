/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import LeanPool.DirectedTopologyLean4.Dipath
import LeanPool.DirectedTopologyLean4.DTop

/-
  This file contains definitions about interpolating points in the directed unit interval
  and contains conditions about when interpolating gives directed maps.
-/

open scoped unitInterval

universe u

section

lemma interp_mem_I (T a b : I) : (σ T : ℝ) * ↑a + ↑T * ↑b ∈ I := by
  have ha₁ : (0 : ℝ) ≤ a := a.2.1
  have ha₂ : (a : ℝ) ≤ 1 := a.2.2
  have hb₁ : (0 : ℝ) ≤ b := b.2.1
  have hb₂ : (b : ℝ) ≤ 1 := b.2.2
  have hT₁ : (0 : ℝ) ≤ T := T.2.1
  have hT₂ : (T : ℝ) ≤ 1 := T.2.2
  have hσT₁ : (0 : ℝ) ≤ σ T := (σ T).2.1
  have hσT₂ : (σ T : ℝ) = 1 - T := by simp [unitInterval.symm]
  refine ⟨?_, ?_⟩
  · nlinarith
  · nlinarith

lemma interp_left_mem_I (T a : I) : (σ T : ℝ) * ↑a + ↑T ∈ I := by
  convert interp_mem_I T a 1
  simp

lemma interp_right_mem_I (T b : I) : (σ T : ℝ) + ↑T * ↑b ∈ I := by
  convert interp_mem_I T 1 b
  simp

lemma interp_const_le_of_le_of_le {a b T₀ T₁ : I} (hab : a ≤ b) (hT : T₀ ≤ T₁) :
  ((σ T₀ : ℝ) * ↑a + ↑T₀ * ↑b) ≤ (σ T₁ : ℝ) * ↑a + ↑T₁ * ↑b := by
  have h₁ : (T₀ : ℝ) * (b - a) ≤ T₁ * (b - a) :=
    mul_le_mul_of_nonneg_right hT (sub_nonneg_of_le hab)
  have hσT₀ : (σ T₀ : ℝ) = 1 - T₀ := by simp [unitInterval.symm]
  have hσT₁ : (σ T₁ : ℝ) = 1 - T₁ := by simp [unitInterval.symm]
  rw [hσT₀, hσT₁]
  nlinarith

/-- The continuous map `t ↦ (1 - t) * a + t * b` interpolating between `a` and `b` in `I`. -/
def interpolate_const (a b : I) : C(I, I) where
  toFun := fun t => ⟨_, interp_mem_I t a b⟩

/-- The directed-map version of `interpolate_const` when `a ≤ b`. -/
def directed_interpolate_const {a b : I} (h : a ≤ b) : D(I,I) where
  toContinuousMap := interpolate_const a b
  directed_toFun := fun _ _ _ hγ _ _ hxy => interp_const_le_of_le_of_le h (hγ hxy)

variable (f g : C(I, I))

/-- Two-parameter interpolation `(s, t) ↦ (1 - s) * f t + s * g t`. -/
def interpolate : C(I × I, I) where
  toFun := fun t => ⟨(σ t.1 : ℝ) * (f t.2) + t.1 * (g t.2), interp_mem_I t.1 (f t.2) (g t.2)⟩

lemma interpolate_left : (interpolate f g).curry 0 = f := by
  ext
  simp [interpolate]

lemma interpolate_right : (interpolate f g).curry 1 = g := by
  ext
  simp [interpolate]

lemma interpolate_constant_apply (t v : I) (hf : f t = v) (hg : g t = v) :
    ∀ x, interpolate f g (x, t) = v := by
  intro x
  simp [interpolate, hf, hg]
  ring_nf

end

section

variable (f g : D(I,I))

lemma directed_interpolate (h : ∀ t, f t ≤ g t) :
    DirectedMap.Directed (interpolate f.toContinuousMap g.toContinuousMap) := by
  intros t₀ t₁ γ γ_dipath x y hxy
  let a₀ := (γ x).1
  let a₁ := (γ x).2
  let b₀ := (γ y).1
  let b₁ := (γ y).2
  have hfab : (f a₁ : ℝ) ≤ f b₁ := DirectedUnitInterval.monotone_of_directed f (γ_dipath.2 hxy)
  have hgab : (g a₁ : ℝ) ≤ g b₁ := DirectedUnitInterval.monotone_of_directed g (γ_dipath.2 hxy)
  have hga₁ : (f a₁ : ℝ) ≤ g a₁ := h a₁
  have ha₀ : (0 : ℝ) ≤ a₀ := a₀.2.1
  have ha₀' : (a₀ : ℝ) ≤ 1 := a₀.2.2
  have hb₀ : (0 : ℝ) ≤ b₀ := b₀.2.1
  have hb₀' : (b₀ : ℝ) ≤ 1 := b₀.2.2
  have ha₀b₀ : (a₀ : ℝ) ≤ b₀ := γ_dipath.1 hxy
  apply Subtype.coe_le_coe.mp
  change (1 - a₀ : ℝ) * (f a₁ : ℝ) + (a₀ : ℝ) * (g a₁ : ℝ) ≤
      (1 - b₀ : ℝ) * (f b₁ : ℝ) + (b₀ : ℝ) * (g b₁ : ℝ)
  nlinarith

end
