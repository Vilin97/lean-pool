/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.MarkovMorphism
import LeanPool.CencovPetz.MonotoneMetric
import Mathlib.LinearAlgebra.BilinearForm.Properties


/-!
# `CencovPetz.LeftInverseIsometry`

For a monotone metric family (Čencov setting), any Markov morphism that admits a left inverse on:

- simplex points (`pushforward`), and
- tangent vectors (`tangentPushforward`)

is an isometry for the metric family.

This is the abstract lemma behind permutation invariance and replication invariance.
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

universe u

namespace MonotoneMetricFamily

lemma comp_eq_of_left_inverse (G : MonotoneMetricFamily) {α β : Type u} [Fintype α] [Fintype β]
    (κ : MarkovMorphism α β) (κ' : MarkovMorphism β α) (p : Simplex α)
    (hp : κ'.pushforward (κ.pushforward p) = p)
    (ht : ∀ u : tangentSpace (α := α), κ'.tangentPushforward (κ.tangentPushforward u) = u) :
    (G.g (α := β) (κ.pushforward p)).comp κ.tangentPushforwardLinear κ.tangentPushforwardLinear
      = G.g (α := α) p := by
  classical
  have hSymm₁ :
      ((G.g (α := β) (κ.pushforward p)).comp
        κ.tangentPushforwardLinear κ.tangentPushforwardLinear).IsSymm := by
    refine ⟨fun u v => ?_⟩
    simp [LinearMap.BilinForm.comp_apply, G.symm (α := β) (p := κ.pushforward p)]
  have hSymm₂ : (G.g (α := α) p).IsSymm := by
    refine ⟨fun u v => ?_⟩
    simpa using (G.symm (α := α) (p := p) u v)
  have hdiag : ∀ u : tangentSpace (α := α),
      ((G.g (α := β) (κ.pushforward p)).comp
        κ.tangentPushforwardLinear κ.tangentPushforwardLinear) u u
          = (G.g (α := α) p) u u := by
    intro u
    have h_le :
        G.g (α := β) (κ.pushforward p) (κ.tangentPushforward u) (κ.tangentPushforward u) ≤
          G.g (α := α) p u u := by
      simpa using (G.monotone (α := α) (β := β) κ p u)
    have h_ge :
        G.g (α := α) p u u ≤
          G.g (α := β) (κ.pushforward p) (κ.tangentPushforward u) (κ.tangentPushforward u) := by
      have h :=
        G.monotone (α := β) (β := α) κ' (κ.pushforward p) (κ.tangentPushforward u)
      -- Simplify using the left-inverse hypotheses.
      simpa [hp, ht u] using h
    have hEq :
        G.g (α := β) (κ.pushforward p) (κ.tangentPushforward u) (κ.tangentPushforward u) =
          G.g (α := α) p u u :=
      le_antisymm h_le h_ge
    simp [LinearMap.BilinForm.comp_apply, MarkovMorphism.tangentPushforwardLinear_apply, hEq]
  exact LinearMap.BilinForm.ext_of_isSymm hSymm₁ hSymm₂ hdiag

lemma eq_of_left_inverse (G : MonotoneMetricFamily) {α β : Type u} [Fintype α] [Fintype β]
    (κ : MarkovMorphism α β) (κ' : MarkovMorphism β α) (p : Simplex α)
    (hp : κ'.pushforward (κ.pushforward p) = p)
    (ht : ∀ u : tangentSpace (α := α), κ'.tangentPushforward (κ.tangentPushforward u) = u)
    (u v : tangentSpace (α := α)) :
    G.g (α := β) (κ.pushforward p) (κ.tangentPushforward u) (κ.tangentPushforward v) =
      G.g (α := α) p u v := by
  have h := comp_eq_of_left_inverse (G := G) κ κ' p hp ht
  simpa [LinearMap.BilinForm.comp_apply, MarkovMorphism.tangentPushforwardLinear_apply] using
    congrArg (fun B : LinearMap.BilinForm ℝ (tangentSpace (α := α)) => B u v) h

end MonotoneMetricFamily
end LeanPool.CencovPetz
