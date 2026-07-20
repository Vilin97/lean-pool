/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.LeftInverseIsometry
import LeanPool.CencovPetz.SufficientStatistic


/-!
# `CencovPetz.PermutationInvariance`

Bridge deterministic sufficient statistics and deterministic Markov morphisms, and derive
permutation/equivalence invariance consequences for monotone metric families in the finite
Čencov/Chentsov setting.

## Main results

- `CencovPetz.MarkovMorphism.deterministic_pushforward_eq_simplex_pushforward`:
  deterministic Markov pushforward agrees with the fiberwise-sum pushforward from
  `SufficientStatistic`.
- `CencovPetz.MonotoneMetricFamily.comp_eq_of_equiv`:
  any monotone metric family is invariant under equivalences (permutations) of finite types.
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

universe u

variable {α β : Type u} [Fintype α] [Fintype β]

namespace MarkovMorphism

lemma deterministic_pushforward_eq_simplex_pushforward [DecidableEq β] (g : α → β)
    (hg : Function.Surjective g) (p : Simplex α) :
    (MarkovMorphism.deterministic (α := α) (β := β) g hg).pushforward p =
      Simplex.pushforward (α := α) (β := β) g hg p := by
  ext b
  simpa [Simplex.pushforward_apply] using
    (MarkovMorphism.deterministic_pushforward_apply (α := α) (β := β) (g := g) (hg := hg) p b)

lemma deterministic_tangentPushforward_eq_tangentPushforward [DecidableEq β] (g : α → β)
    (hg : Function.Surjective g) (u : tangentSpace (α := α)) :
    (MarkovMorphism.deterministic (α := α) (β := β) g hg).tangentPushforward u =
      _root_.LeanPool.CencovPetz.tangentPushforward (α := α) (β := β) g u := by
  ext b
  simpa [_root_.LeanPool.CencovPetz.tangentPushforward_apply] using
    (MarkovMorphism.deterministic_tangentPushforward_apply
      (α := α) (β := β) (g := g) (hg := hg) u b)

lemma deterministic_pushforward_apply_of_equiv
    (e : α ≃ β) (p : Simplex α) (b : β) :
    ((MarkovMorphism.deterministic (α := α) (β := β)
        (g := (e : α → β)) e.surjective).pushforward
        p).p b =
      p.p (e.symm b) := by
  classical
  have hs : (Finset.univ.filter fun a : α => e a = b) = {e.symm b} := by
    ext a
    simp [e.apply_eq_iff_eq_symm_apply]
  calc
    ((MarkovMorphism.deterministic (α := α) (β := β)
          (g := (e : α → β))
          e.surjective).pushforward p).p b
        = ∑ a with e a = b, p.p a := by
              simpa using
                (MarkovMorphism.deterministic_pushforward_apply
                  (α := α) (β := β) (g := (e : α → β))
                  (hg := e.surjective) p b)
    _ = p.p (e.symm b) := by simp [hs]

lemma deterministic_tangentPushforward_apply_of_equiv
    (e : α ≃ β) (u : tangentSpace (α := α)) (b : β) :
    ((MarkovMorphism.deterministic (α := α) (β := β)
        (g := (e : α → β))
        e.surjective).tangentPushforward
        u : β → ℝ) b =
      (u : α → ℝ) (e.symm b) := by
  classical
  have hs : (Finset.univ.filter fun a : α => e a = b) = {e.symm b} := by
    ext a
    simp [e.apply_eq_iff_eq_symm_apply]
  calc
    ((MarkovMorphism.deterministic (α := α) (β := β)
          (g := (e : α → β))
          e.surjective).tangentPushforward
          u : β → ℝ) b
        = ∑ a with e a = b, (u : α → ℝ) a := by
              simpa using
                (MarkovMorphism.deterministic_tangentPushforward_apply
                  (α := α) (β := β)
                  (g := (e : α → β))
                  (hg := e.surjective) u b)
    _ = (u : α → ℝ) (e.symm b) := by simp [hs]

lemma deterministic_pushforward_comp_symm
    (e : α ≃ β) (p : Simplex α) :
    (MarkovMorphism.deterministic (α := β) (β := α)
        (g := (e.symm : β → α))
        e.symm.surjective).pushforward
      ((MarkovMorphism.deterministic (α := α) (β := β)
          (g := (e : α → β))
          e.surjective).pushforward p)
      = p := by
  classical
  ext a
  -- Evaluate both pushforwards using the explicit
  -- "equivalence" formulas.
  calc
    ((MarkovMorphism.deterministic (α := β) (β := α)
          (g := (e.symm : β → α))
          e.symm.surjective).pushforward
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).pushforward p)).p a
        =
          ((MarkovMorphism.deterministic (α := α) (β := β)
              (g := (e : α → β))
              e.surjective).pushforward p).p
            (e a) := by
              simpa using
                (deterministic_pushforward_apply_of_equiv
                  (α := β) (β := α) (e := e.symm)
                  (p :=
                    (MarkovMorphism.deterministic
                      (α := α) (β := β)
                      (g := (e : α → β))
                      e.surjective).pushforward p)
                  (b := a))
    _ = p.p a := by
          simpa using
            (deterministic_pushforward_apply_of_equiv
              (α := α) (β := β) (e := e)
              (p := p) (b := e a))

lemma deterministic_tangentPushforward_comp_symm
    (e : α ≃ β) (u : tangentSpace (α := α)) :
    (MarkovMorphism.deterministic (α := β) (β := α)
        (g := (e.symm : β → α))
        e.symm.surjective).tangentPushforward
      ((MarkovMorphism.deterministic (α := α) (β := β)
          (g := (e : α → β))
          e.surjective).tangentPushforward u)
      = u := by
  classical
  ext a
  -- Evaluate both pushforwards using the explicit
  -- "equivalence" formulas.
  calc
    ((MarkovMorphism.deterministic (α := β) (β := α)
          (g := (e.symm : β → α))
          e.symm.surjective).tangentPushforward
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforward
            u) : α → ℝ) a
        =
          ((MarkovMorphism.deterministic (α := α) (β := β)
              (g := (e : α → β))
              e.surjective).tangentPushforward
              u : β → ℝ)
            (e a) := by
              simpa using
                (deterministic_tangentPushforward_apply_of_equiv
                  (α := β) (β := α) (e := e.symm)
                  (u :=
                    (MarkovMorphism.deterministic
                      (α := α) (β := β)
                      (g := (e : α → β))
                      e.surjective).tangentPushforward u)
                  (b := a))
    _ = (u : α → ℝ) a := by
          simpa using
            (deterministic_tangentPushforward_apply_of_equiv
              (α := α) (β := β) (e := e)
              (u := u) (b := e a))

end MarkovMorphism

namespace MonotoneMetricFamily

lemma comp_eq_of_equiv
    (G : MonotoneMetricFamily) (e : α ≃ β) (p : Simplex α) :
    (G.g (α := β)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).pushforward p)).comp
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforwardLinear)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforwardLinear)
      = G.g (α := α) p := by
  classical
  let κ : MarkovMorphism α β :=
    MarkovMorphism.deterministic (α := α) (β := β)
      (g := (e : α → β)) e.surjective
  let κ' : MarkovMorphism β α :=
    MarkovMorphism.deterministic (α := β) (β := α)
      (g := (e.symm : β → α)) e.symm.surjective
  refine MonotoneMetricFamily.comp_eq_of_left_inverse
    (G := G) (κ := κ) (κ' := κ') (p := p) ?_ ?_
  · simpa [κ, κ'] using
      MarkovMorphism.deterministic_pushforward_comp_symm
        (α := α) (β := β) (e := e) (p := p)
  · intro u
    simpa [κ, κ'] using
      MarkovMorphism.deterministic_tangentPushforward_comp_symm
        (α := α) (β := β) (e := e) (u := u)

lemma eq_of_equiv
    (G : MonotoneMetricFamily) (e : α ≃ β) (p : Simplex α)
    (u v : tangentSpace (α := α)) :
    G.g (α := β)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).pushforward p)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforward u)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforward v)
      = G.g (α := α) p u v := by
  classical
  let κ : MarkovMorphism α β :=
    MarkovMorphism.deterministic (α := α) (β := β)
      (g := (e : α → β)) e.surjective
  let κ' : MarkovMorphism β α :=
    MarkovMorphism.deterministic (α := β) (β := α)
      (g := (e.symm : β → α)) e.symm.surjective
  refine MonotoneMetricFamily.eq_of_left_inverse
    (G := G) (κ := κ) (κ' := κ') (p := p) ?_ ?_ u v
  · simpa [κ, κ'] using
      MarkovMorphism.deterministic_pushforward_comp_symm
        (α := α) (β := β) (e := e) (p := p)
  · intro u
    simpa [κ, κ'] using
      MarkovMorphism.deterministic_tangentPushforward_comp_symm
        (α := α) (β := β) (e := e) (u := u)

end MonotoneMetricFamily
end LeanPool.CencovPetz
