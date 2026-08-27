/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/- Semantic invariance under an injective embedding of variable names. -/
import LeanPool.MatchingLogic.EntryIII.Injection

/-!
# MatchingLogic.EntryIII.EmbeddingSemantics
-/

namespace MatchingLogic

variable {S : Signature} {Var Var' : Type}

/-- Denotation commutes with an injective variable embedding. -/
theorem Model.denote_renameInjective [DecidableEq Var] [DecidableEq Var']
    (M : Model S) (f : Var → Var') (hf : Function.Injective f)
    (rho : Var' → M.carrier) (p : Pattern S Var) :
    M.denote rho (p.rename f) = M.denote (rho ∘ f) p := by
  induction p generalizing rho with
  | var x => rfl
  | bot => rfl
  | app sigma args ih =>
      simp only [Pattern.rename, denote_app]
      congr 2
      funext i
      exact ih i rho
  | imp phi psi ihphi ihpsi =>
      simp only [Pattern.rename, denote_imp]
      rw [ihphi rho, ihpsi rho]
  | ex x phi ih =>
      simp only [Pattern.rename, denote_ex]
      congr 1
      funext a
      rw [ih]
      congr 1
      funext z
      by_cases hzx : z = x
      · subst z
        simp
      · have hfx : f z ≠ f x := fun heq => hzx (hf heq)
        simp [hzx, hfx]

/-- Conjunctive denotation commutes with an injective variable embedding. -/
theorem Model.denoteSet_renameInjective [DecidableEq Var] [DecidableEq Var']
    (M : Model S) (f : Var → Var') (hf : Function.Injective f)
    (rho : Var' → M.carrier) (Delta : Set (Pattern S Var)) :
    M.denoteSet rho (Pattern.rename f '' Delta) =
      M.denoteSet (rho ∘ f) Delta := by
  ext u
  simp only [Model.denoteSet, Set.mem_iInter]
  constructor
  · intro h p hp
    have hu := h (p.rename f) ⟨p, hp, rfl⟩
    rwa [M.denote_renameInjective f hf] at hu
  · intro h p hp
    rcases hp with ⟨q, hq, rfl⟩
    rw [M.denote_renameInjective f hf]
    exact h q hq

/-- Local consequence is invariant under an injective change to a larger name space. -/
theorem localCons_renameInjective [DecidableEq Var] [DecidableEq Var']
    (f : Var → Var') (hf : Function.Injective f)
    {Delta : Set (Pattern S Var)} {phi : Pattern S Var} :
    LocalCons Delta phi ↔
      LocalCons (Pattern.rename f '' Delta) (phi.rename f) := by
  constructor
  · intro h M rho
    rw [M.denoteSet_renameInjective f hf, M.denote_renameInjective f hf]
    exact h M (rho ∘ f)
  · intro h M rho
    classical
    let rho' : Var' → M.carrier :=
      Function.extend f rho (fun _ => Classical.choice M.nonempty)
    have hrho : rho' ∘ f = rho := by
      funext x
      exact hf.extend_apply rho (fun _ => Classical.choice M.nonempty) x
    have h' := h M rho'
    rw [M.denoteSet_renameInjective f hf, M.denote_renameInjective f hf] at h'
    simpa only [hrho] using h'

end MatchingLogic
