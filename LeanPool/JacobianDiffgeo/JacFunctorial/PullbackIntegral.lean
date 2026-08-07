/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.JacFunctorial.Pullback
import LeanPool.JacobianDiffgeo.Path

/-!
# Path-integral naturality (jacobian-functoriality §4)

Unit: jacobian-functoriality. `IsPrimitiveAlongMap.pullback_comp` (a general reusable lemma: a
primitive of `η` along `f ∘ K` pulls back to a primitive of `Form1.pullback f hf η` along `K`)
and its corollary `pathIntegral_pullback` (naturality of `pathIntegral` under pullback).
-/

open scoped ContDiff Manifold Topology unitInterval
open Set Filter IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {α : Type*} [TopologicalSpace α]

/-- A primitive of `η` along `f ∘ K` pulls back to a primitive of `Form1.pullback f hf η`
along `K` (§4.2). -/
theorem IsPrimitiveAlongMap.pullback_comp {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    {K : α → X} {s : Set α} (hK : ContinuousOn K s) {η : Form1 Y} {F : α → ℂ}
    (h : IsPrimitiveAlongMap (f ∘ K) η F s) :
    IsPrimitiveAlongMap K (Form1.pullback f hf η) F s := by
  intro a ha
  obtain ⟨e', he', hfKa, g, hg, hF⟩ := h a ha
  set e := chartAt ℂ (K a) with he_def
  set φ : ℂ → ℂ := ⇑e' ∘ f ∘ ⇑e.symm with hφ_def
  refine ⟨e, chart_mem_maximalAtlas (K a), mem_chart_source ℂ (K a), g ∘ φ, ?_, ?_⟩
  · -- `HasDerivAt` of the composite `g ∘ φ`, near `e (K a)`.
    have hpt0Eq : f (⇑e.symm (e (K a))) = f (K a) := by
      rw [e.left_inv (mem_chart_source ℂ (K a))]
    have hcont : ContinuousAt (f ∘ ⇑e.symm) (e (K a)) := by
      have hg0 : ContinuousAt f (⇑e.symm (e (K a))) := by
        rw [e.left_inv (mem_chart_source ℂ (K a))]; exact (hf (K a)).continuousAt
      exact hg0.comp (e.continuousAt_symm (mem_chart_target ℂ (K a)))
    have hmemF : (f ∘ ⇑e.symm) (e (K a)) ∈ e'.source := by
      simp only [Function.comp_apply, hpt0Eq]; exact hfKa
    have hφcont : Tendsto φ (𝓝 (e (K a))) (𝓝 (φ (e (K a)))) := by
      have : Tendsto (⇑e' ∘ f ∘ ⇑e.symm) (𝓝 (e (K a)))
          (𝓝 ((⇑e' ∘ f ∘ ⇑e.symm) (e (K a)))) := (e'.continuousAt hmemF).comp hcont
      exact this
    have hφeq0 : φ (e (K a)) = e' (f (K a)) := by
      change e' ((f ∘ ⇑e.symm) (e (K a))) = e' (f (K a))
      simp only [Function.comp_apply, hpt0Eq]
    have hg' : ∀ᶠ z in 𝓝 (e (K a)), HasDerivAt g (coeffIn e' η (φ z)) (φ z) := by
      have hg2 : ∀ᶠ w in 𝓝 (φ (e (K a))), HasDerivAt g (coeffIn e' η w) w := by
        rw [hφeq0]; exact hg
      exact hφcont.eventually hg2
    filter_upwards [hcont.preimage_mem_nhds (e'.open_source.mem_nhds hmemF),
      e.open_target.mem_nhds (mem_chart_target ℂ (K a)), hg'] with z hz hzt hgz
    have hz' : f (⇑e.symm z) ∈ e'.source := hz
    have hφAt : AnalyticAt ℂ φ z := by
      have hA := analyticAt_of_mem_maximalAtlas (hf (⇑e.symm z)) (chart_mem_maximalAtlas (K a))
        (e.map_target hzt) he' hz'
      rwa [e.right_inv hzt] at hA
    have hval : coeffIn e (Form1.pullback f hf η) z = coeffIn e' η (φ z) * deriv φ z := by
      rw [coeffIn_pullback f hf η (chart_mem_maximalAtlas (K a)) he' hzt hz', mul_comm]
      rfl
    rw [hval]
    exact hgz.comp z hφAt.differentiableAt.hasDerivAt
  · -- `F` eventually equals `(g ∘ φ) ∘ e ∘ K`.
    have hKcont : ContinuousWithinAt K s a := hK a ha
    have hecont : ContinuousAt e (K a) := e.continuousAt (mem_chart_source ℂ (K a))
    filter_upwards [hF, hKcont.tendsto.eventually (e.open_source.mem_nhds
      (mem_chart_source ℂ (K a)))] with b hb hKb
    refine ⟨hKb, ?_⟩
    rw [hb.2]
    show g (⇑e' ((f ∘ K) b)) = (g ∘ φ) (e (K b))
    congr 1
    change e' (f (K b)) = e' (f (⇑e.symm (e (K b))))
    rw [e.left_inv hKb]

/-! ### Naturality of `pathIntegral` -/

variable {x y : X}

theorem pathIntegral_pullback {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (γ : Path x y)
    (η : Form1 Y) :
    pathIntegral γ (Form1.pullback f hf η) = pathIntegral (γ.map hf.continuous) η := by
  obtain ⟨F, hF, hF0⟩ := exists_isPrimitiveAlong (γ.map hf.continuous) η
  have hmapext : (γ.map hf.continuous).extend = f ∘ γ.extend := by
    funext t
    change (γ.map hf.continuous) (Set.projIcc (0 : ℝ) 1 zero_le_one t) =
      f (γ (Set.projIcc (0 : ℝ) 1 zero_le_one t))
    exact congrFun (Path.map_coe γ hf.continuous) (Set.projIcc (0 : ℝ) 1 zero_le_one t)
  have hF' : IsPrimitiveAlongMap (γ.map hf.continuous).extend η F Set.univ := hF
  have hFcomp : IsPrimitiveAlongMap (f ∘ γ.extend) η F Set.univ := hmapext ▸ hF'
  have hFK : IsPrimitiveAlongMap γ.extend (Form1.pullback f hf η) F Set.univ :=
    IsPrimitiveAlongMap.pullback_comp hf (continuousOn_univ.mpr γ.continuous_extend) hFcomp
  have hprim : IsPrimitiveAlong γ (Form1.pullback f hf η) F := hFK
  rw [hprim.pathIntegral_eq, hF.pathIntegral_eq]

end RS

end
