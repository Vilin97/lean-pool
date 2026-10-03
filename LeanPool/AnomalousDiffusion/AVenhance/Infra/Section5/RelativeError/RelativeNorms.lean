/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeVectorTriangle
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Cube

/-! Triangle inequalities for the actual space-time gradient norm. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory AVenhance
namespace AVenhance.Infra.Section5.RelativeError

theorem RelativeNorms.relative_timeCube_integrable {f : ℝ × Vec 2 → ℝ}
    (hf : ContinuousOn f (Set.Ici (0 : ℝ) ×ˢ Set.univ)) : IntegrableOn f timeCube := by
  let K : Set (ℝ × Vec 2) := Set.Icc (0 : ℝ) 1 ×ˢ
    AVenhance.Infra.Section5.LeftToShow.cubeCl
  have hc : IsCompact K := isCompact_Icc.prod AVenhance.Infra.Section5.LeftToShow.isCompact_cubeCl
  have hsub : K ⊆ Set.Ici (0 : ℝ) ×ˢ Set.univ := fun _ hp => ⟨hp.1.1, Set.mem_univ _⟩
  apply ((hf.mono hsub).integrableOn_compact hc).mono_set
  intro p hp
  exact ⟨⟨hp.1.1.le, hp.1.2.le⟩,
    AVenhance.Infra.Section5.LeftToShow.unitCube_subset_cubeCl hp.2⟩

theorem relative_vecDot_continuousOn {f g : ℝ × Vec 2 → Vec 2} {s : Set (ℝ × Vec 2)}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun p => vecDot (f p) (g p)) s := by
  unfold vecDot
  exact continuousOn_finsetSum _ fun i _ =>
    ((continuous_apply i).comp_continuousOn hf).mul
      ((continuous_apply i).comp_continuousOn hg)

theorem relative_gradient_norm_add_le {f g : ℝ → Vec 2 → Vec 2}
    (hf : ContinuousOn (fun p : ℝ × Vec 2 => f p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hg : ContinuousOn (fun p : ℝ × Vec 2 => g p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    Real.sqrt (spaceTimeGradNormSq (fun t x => f t x + g t x)) ≤
      Real.sqrt (spaceTimeGradNormSq f) + Real.sqrt (spaceTimeGradNormSq g) := by
  exact relative_vector_integral_L2_add
    (RelativeNorms.relative_timeCube_integrable (relative_vecDot_continuousOn hf hf))
    (RelativeNorms.relative_timeCube_integrable (relative_vecDot_continuousOn hg hg))
    (RelativeNorms.relative_timeCube_integrable (relative_vecDot_continuousOn hf hg))

theorem relative_gradient_norm_neg (f : ℝ → Vec 2 → Vec 2) :
    spaceTimeGradNormSq (fun t x => -f t x) = spaceTimeGradNormSq f := by
  unfold spaceTimeGradNormSq
  congr 1
  funext p
  simp only [vecNormSq, vecDot, Pi.neg_apply, neg_mul_neg]

theorem relative_gradient_norm_sub_le {f g : ℝ → Vec 2 → Vec 2}
    (hf : ContinuousOn (fun p : ℝ × Vec 2 => f p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hg : ContinuousOn (fun p : ℝ × Vec 2 => g p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    |Real.sqrt (spaceTimeGradNormSq f) - Real.sqrt (spaceTimeGradNormSq g)| ≤
      Real.sqrt (spaceTimeGradNormSq (fun t x => f t x - g t x)) := by
  have h1 := relative_gradient_norm_add_le (f := fun t x => f t x - g t x) (g := g) (hf.sub hg) hg
  have he1 : (fun t x => (f t x - g t x) + g t x) = f := by
    funext t x; exact sub_add_cancel _ _
  rw [he1] at h1
  have h2 := relative_gradient_norm_add_le (f := fun t x => g t x - f t x) (g := f) (hg.sub hf) hf
  have he2 : (fun t x => (g t x - f t x) + f t x) = g := by
    funext t x; exact sub_add_cancel _ _
  have he3 : (fun t x => g t x - f t x) = fun t x => -(f t x - g t x) := by
    funext t x; exact (neg_sub _ _).symm
  rw [he2, he3, relative_gradient_norm_neg] at h2
  exact abs_le.mpr ⟨by linarith only [h2], by linarith only [h1]⟩

/-- Joint closed-half-line continuity supplies coordinate L2 integrability. -/
theorem relative_gradient_memLp_of_continuous {f : ℝ → Vec 2 → Vec 2}
    (hf : ContinuousOn (fun p : ℝ × Vec 2 => f p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => f p.1 p.2 i) 2
      (volume.restrict timeCube) := by
  intro i
  have hc := (continuous_apply i).comp_continuousOn hf
  have hm := (hc.mono (show timeCube ⊆ Set.Ici (0 : ℝ) ×ˢ Set.univ from
    fun p hp => ⟨hp.1.1.le, Set.mem_univ _⟩)).aestronglyMeasurable (μ := volume)
    (measurableSet_Ioo.prod AVenhance.Infra.Section5.LeftToShow.measurableSet_unitCube')
  exact (memLp_two_iff_integrable_sq hm).2 (RelativeNorms.relative_timeCube_integrable (hc.pow 2))

/-- Dot products of genuine coordinate L2 fields are integrable. -/
theorem relative_gradient_dot_integrable {f g : ℝ → Vec 2 → Vec 2}
    (hf : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => f p.1 p.2 i) 2
      (volume.restrict timeCube))
    (hg : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => g p.1 p.2 i) 2
      (volume.restrict timeCube)) :
    IntegrableOn (fun p : ℝ × Vec 2 => vecDot (f p.1 p.2) (g p.1 p.2)) timeCube := by
  exact integrable_finsetSum Finset.univ fun i _ => (hf i).integrable_mul (hg i)

/-- Reverse gradient triangle inequality using integrability, with no time-zero
regularity premise. -/
theorem relative_gradient_norm_sub_le_of_memLp {f g : ℝ → Vec 2 → Vec 2}
    (hf : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => f p.1 p.2 i) 2
      (volume.restrict timeCube))
    (hg : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => g p.1 p.2 i) 2
      (volume.restrict timeCube)) :
    |Real.sqrt (spaceTimeGradNormSq f) - Real.sqrt (spaceTimeGradNormSq g)| ≤
      Real.sqrt (spaceTimeGradNormSq (fun t x => f t x - g t x)) := by
  have hadd {F G : ℝ → Vec 2 → Vec 2}
      (hF : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => F p.1 p.2 i) 2
        (volume.restrict timeCube))
      (hG : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => G p.1 p.2 i) 2
        (volume.restrict timeCube)) :
      Real.sqrt (spaceTimeGradNormSq (fun t x => F t x + G t x)) ≤
        Real.sqrt (spaceTimeGradNormSq F) + Real.sqrt (spaceTimeGradNormSq G) :=
    relative_vector_integral_L2_add (relative_gradient_dot_integrable hF hF)
      (relative_gradient_dot_integrable hG hG) (relative_gradient_dot_integrable hF hG)
  have h1 := hadd (F := fun t x => f t x - g t x) (G := g)
    (fun i => (hf i).sub (hg i)) hg
  have he1 : (fun t x => (f t x - g t x) + g t x) = f := by
    funext t x; exact sub_add_cancel _ _
  rw [he1] at h1
  have h2 := hadd (F := fun t x => g t x - f t x) (G := f)
    (fun i => (hg i).sub (hf i)) hf
  have he2 : (fun t x => (g t x - f t x) + f t x) = g := by
    funext t x; exact sub_add_cancel _ _
  have he3 : (fun t x => g t x - f t x) = fun t x => -(f t x - g t x) := by
    funext t x; exact (neg_sub _ _).symm
  rw [he2, he3, relative_gradient_norm_neg] at h2
  exact abs_le.mpr ⟨by linarith only [h2], by linarith only [h1]⟩

end AVenhance.Infra.Section5.RelativeError
