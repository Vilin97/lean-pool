/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Variable transport for entry point (iii).

The source paper fixes a countably infinite set of element variables and treats
alpha-equivalent patterns as identical.  The verified base deliberately uses
raw named syntax instead.  This additive layer supplies the first missing
bridge: transport of syntax, contexts, derivations, semantics, and strong local
completeness along an equivalence of variable types.
-/
import LeanPool.MatchingLogic.ProofSystem
import Mathlib.Logic.Denumerable

/-!
# MatchingLogic.EntryIII.Renaming
-/

namespace MatchingLogic

variable {S : Signature} {Var Var' Var'' : Type}

namespace Pattern

/-- Rename every free and bound element-variable occurrence. -/
def rename (f : Var → Var') : Pattern S Var → Pattern S Var'
  | .var x => .var (f x)
  | .app σ args => .app σ (fun i => (args i).rename f)
  | .imp φ ψ => .imp (φ.rename f) (ψ.rename f)
  | .bot => .bot
  | .ex x φ => .ex (f x) (φ.rename f)

@[simp] theorem rename_id (p : Pattern S Var) : p.rename id = p := by
  induction p with
  | var x => rfl
  | app σ args ih =>
      simp only [rename]
      congr
      funext i
      exact ih i
  | imp φ ψ ihφ ihψ => simp [rename, ihφ, ihψ]
  | bot => rfl
  | ex x φ ih => simp [rename, ih]

@[simp] theorem rename_comp (g : Var' → Var'') (f : Var → Var')
    (p : Pattern S Var) :
    (p.rename f).rename g = p.rename (g ∘ f) := by
  induction p with
  | var x => rfl
  | app σ args ih =>
      simp only [rename]
      congr
      funext i
      exact ih i
  | imp φ ψ ihφ ihψ => simp [rename, ihφ, ihψ]
  | bot => rfl
  | ex x φ ih => simp [rename, ih]

/-- Free-variable membership commutes with a bijective renaming. -/
theorem mem_FV_renameEquiv
    (e : Var ≃ Var') (p : Pattern S Var) (y : Var') :
    y ∈ FV (p.rename e) ↔ e.symm y ∈ FV p := by
  classical
  induction p with
  | var x =>
      simp only [rename, FV_var, Set.mem_singleton_iff]
      constructor
      · intro h
        simpa using congrArg e.symm h
      · intro h
        simpa using congrArg e h
  | app σ args ih =>
      simp only [rename, FV_app, Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (ih i).mp hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, (ih i).mpr hi⟩
  | imp φ ψ ihφ ihψ => simp [rename, ihφ, ihψ]
  | bot => simp [rename]
  | ex x φ ih =>
      simp only [rename, FV_ex, Set.mem_sdiff, Set.mem_singleton_iff, ih]
      apply and_congr Iff.rfl
      apply not_congr
      constructor
      · intro h
        simpa using congrArg e.symm h
      · intro h
        simpa using congrArg e h

/-- Variable-for-variable substitution commutes with a bijective renaming. -/
theorem substVar_renameEquiv [DecidableEq Var] [DecidableEq Var']
    (e : Var ≃ Var') (x y : Var) (p : Pattern S Var) :
    (substVar x y p).rename e = substVar (e x) (e y) (p.rename e) := by
  induction p with
  | var z =>
      by_cases hzx : z = x
      · simp [substVar, rename, hzx]
      · simp [substVar, rename, hzx, e.injective.eq_iff]
  | app σ args ih =>
      simp only [substVar, rename]
      congr
      funext i
      exact ih i
  | imp φ ψ ihφ ihψ => simp [substVar, rename, ihφ, ihψ]
  | bot => rfl
  | ex z φ ih =>
      by_cases hzx : z = x
      · simp [substVar, rename, hzx]
      · simp [substVar, rename, hzx, e.injective.eq_iff, ih]

/-- A bijective renaming preserves the capture-freedom side condition. -/
theorem captureFree_renameEquiv
    (e : Var ≃ Var') {x y : Var} {p : Pattern S Var}
    (h : CaptureFree x y p) :
    CaptureFree (e x) (e y) (p.rename e) := by
  classical
  induction p generalizing x y with
  | var z => trivial
  | bot => trivial
  | app σ args ih =>
      intro i
      exact ih i (h i)
  | imp φ ψ ihφ ihψ =>
      exact ⟨ihφ h.1, ihψ h.2⟩
  | ex z φ ih =>
      rcases h with hzx | hfree | ⟨hzy, hrec⟩
      · exact Or.inl (congrArg e hzx)
      · apply Or.inr (Or.inl ?_)
        intro hmem
        apply hfree
        simpa using (mem_FV_renameEquiv e φ (e x)).mp hmem
      · exact Or.inr (Or.inr ⟨fun heq => hzy (e.injective heq), ih hrec⟩)

/-- Renaming a tuple commutes with replacing one argument. -/
theorem rename_update (f : Var → Var') {n : Nat}
    (args : Fin n → Pattern S Var) (i : Fin n) (p : Pattern S Var) :
    (fun j => (Function.update args i p j).rename f) =
      Function.update (fun j => (args j).rename f) i (p.rename f) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

end Pattern

/-- Renaming commutes with propositional substitution. -/
theorem PForm.subst_rename (f : Var → Var') (p : PForm)
    (theta : Nat → Pattern S Var) :
    (p.subst theta).rename f = p.subst (fun n => (theta n).rename f) := by
  induction p with
  | atom n => rfl
  | bot => rfl
  | imp p q ihp ihq => simp [PForm.subst, Pattern.rename, ihp, ihq]

/-- Rename every variable occurrence in an application context. -/
def AppCtx.rename (f : Var → Var') : AppCtx S Var → AppCtx S Var'
  | .hole => .hole
  | .node σ i args C => .node σ i (fun j => (args j).rename f) (C.rename f)

/-- Renaming commutes with plugging an application context. -/
theorem AppCtx.plug_renameEquiv
    (e : Var ≃ Var') (C : AppCtx S Var) (p : Pattern S Var) :
    (C.plug p).rename e = (C.rename e).plug (p.rename e) := by
  induction C with
  | hole => rfl
  | node σ i args C ih =>
      simp only [AppCtx.plug, AppCtx.rename, Pattern.rename]
      congr
      funext j
      by_cases hji : j = i
      · subst j
        simpa using ih
      · simp [hji]

/-- Renaming distributes through finite conjunction. -/
theorem rename_conj (f : Var → Var') (l : List (Pattern S Var)) :
    (conj l).rename f = conj (l.map (Pattern.rename f)) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [conj, Pattern.and, Pattern.nt, Pattern.rename, ih]

/-- Denotation is unchanged by a bijective change of variable names. -/
theorem Model.denote_renameEquiv [DecidableEq Var] [DecidableEq Var']
    (M : Model S) (e : Var ≃ Var') (rho : Var' → M.carrier)
    (p : Pattern S Var) :
    M.denote rho (p.rename e) = M.denote (rho ∘ e) p := by
  induction p generalizing rho with
  | var x => rfl
  | bot => rfl
  | app σ args ih =>
      simp only [Pattern.rename, denote_app]
      congr 2
      funext i
      exact ih i rho
  | imp φ ψ ihφ ihψ =>
      simp only [Pattern.rename, denote_imp]
      rw [ihφ rho, ihψ rho]
  | ex x φ ih =>
      simp only [Pattern.rename, denote_ex]
      congr 1
      funext a
      rw [ih]
      congr 1
      funext z
      by_cases hzx : z = x
      · subst z
        simp
      · have hezx : e z ≠ e x := fun heq => hzx (e.injective heq)
        simp [hzx, hezx]

/-- Conjunctive denotation of a theory is unchanged by a bijective renaming. -/
theorem Model.denoteSet_renameEquiv [DecidableEq Var] [DecidableEq Var']
    (M : Model S) (e : Var ≃ Var') (rho : Var' → M.carrier)
    (Delta : Set (Pattern S Var)) :
    M.denoteSet rho (Pattern.rename e '' Delta) = M.denoteSet (rho ∘ e) Delta := by
  ext u
  simp only [Model.denoteSet, Set.mem_iInter]
  constructor
  · intro h p hp
    have hu := h (p.rename e) ⟨p, hp, rfl⟩
    rwa [M.denote_renameEquiv] at hu
  · intro h p hp
    rcases hp with ⟨q, hq, rfl⟩
    rw [M.denote_renameEquiv]
    exact h q hq

/-- Derivability is invariant under a bijective change of variable names. -/
theorem Provable.renameEquiv [DecidableEq Var] [DecidableEq Var']
    (e : Var ≃ Var') {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (h : Provable Gamma phi) :
    Provable (Pattern.rename e '' Gamma) (phi.rename e) := by
  induction h with
  | hyp hphi => exact .hyp ⟨_, hphi, rfl⟩
  | taut hp =>
      rw [PForm.subst_rename]
      exact .taut hp
  | mp hphi himp ihphi ihimp => exact .mp ihphi ihimp
  | exQuant hfree =>
      simpa [Pattern.rename, Pattern.substVar_renameEquiv] using
        (Provable.exQuant (Γ := Pattern.rename e '' Gamma)
          (Pattern.captureFree_renameEquiv e hfree))
  | exGen himp hfree ih =>
      apply Provable.exGen ih
      intro hmem
      apply hfree
      simpa using (Pattern.mem_FV_renameEquiv e _ (e _)).mp hmem
  | @propBot σ i args =>
      simpa [Pattern.rename, Pattern.rename_update] using
        (Provable.propBot (Γ := Pattern.rename e '' Gamma)
          (σ := σ) (i := i) (args := fun j => (args j).rename e))
  | @propOr σ i args phi₁ phi₂ =>
      simpa [Pattern.rename, Pattern.or, Pattern.nt, Pattern.rename_update] using
        (Provable.propOr (Γ := Pattern.rename e '' Gamma)
          (σ := σ) (i := i) (args := fun j => (args j).rename e)
          (φ₁ := phi₁.rename e) (φ₂ := phi₂.rename e))
  | @propEx σ i args x phi hfree =>
      have hfree' : ∀ j, j ≠ i → e x ∉ FV ((args j).rename e) := by
        intro j hji hmem
        apply hfree j hji
        simpa using (Pattern.mem_FV_renameEquiv e (args j) (e x)).mp hmem
      simpa [Pattern.rename, Pattern.rename_update] using
        (Provable.propEx (Γ := Pattern.rename e '' Gamma)
          (σ := σ) (i := i) (args := fun j => (args j).rename e)
          (x := e x) (φ := phi.rename e) hfree')
  | @framing σ i args phi₁ phi₂ himp ih =>
      simpa [Pattern.rename, Pattern.rename_update] using
        (Provable.framing (Γ := Pattern.rename e '' Gamma)
          (σ := σ) (i := i) (args := fun j => (args j).rename e) ih)
  | @existence x =>
      simpa [Pattern.rename] using
        (Provable.existence (Γ := Pattern.rename e '' Gamma) (x := e x))
  | @singleton x phi C₁ C₂ =>
      simpa [AppCtx.plug_renameEquiv, Pattern.rename, Pattern.and, Pattern.nt] using
        (Provable.singleton (Γ := Pattern.rename e '' Gamma) (x := e x)
          (φ := phi.rename e) (C₁.rename e) (C₂.rename e))

/-- Local consequence is invariant under a bijective change of variable names. -/
theorem localCons_renameEquiv [DecidableEq Var] [DecidableEq Var']
    (e : Var ≃ Var') {Delta : Set (Pattern S Var)} {phi : Pattern S Var} :
    LocalCons Delta phi ↔ LocalCons (Pattern.rename e '' Delta) (phi.rename e) := by
  constructor
  · intro h M rho
    rw [M.denoteSet_renameEquiv, M.denote_renameEquiv]
    exact h M (rho ∘ e)
  · intro h M rho
    have h' := h M (rho ∘ e.symm)
    rw [M.denoteSet_renameEquiv, M.denote_renameEquiv] at h'
    simpa [Function.comp_def] using h'

/-- Strong local completeness depends only on the variable type up to equivalence. -/
theorem strongLocalCompleteness_congr [DecidableEq Var] [DecidableEq Var']
    (e : Var ≃ Var') :
    StrongLocalCompleteness S Var ↔ StrongLocalCompleteness S Var' := by
  constructor
  · intro h
    rw [StrongLocalCompleteness] at h ⊢
    intro Delta phi hlocal
    have hlocal' :
        LocalCons (Pattern.rename e.symm '' Delta) (phi.rename e.symm) :=
      (localCons_renameEquiv e.symm).mp hlocal
    obtain ⟨l, hl, hp⟩ := h _ _ hlocal'
    refine ⟨l.map (Pattern.rename e), ?_, ?_⟩
    · intro delta hdelta
      obtain ⟨q, hql, rfl⟩ := List.mem_map.mp hdelta
      obtain ⟨d, hd, rfl⟩ := hl q hql
      simpa [Pattern.rename_comp] using hd
    · have hp' := hp.renameEquiv e
      simpa [Pattern.rename, rename_conj, Pattern.rename_comp] using hp'
  · intro h
    rw [StrongLocalCompleteness] at h ⊢
    intro Delta phi hlocal
    have hlocal' :
        LocalCons (Pattern.rename e '' Delta) (phi.rename e) :=
      (localCons_renameEquiv e).mp hlocal
    obtain ⟨l, hl, hp⟩ := h _ _ hlocal'
    refine ⟨l.map (Pattern.rename e.symm), ?_, ?_⟩
    · intro delta hdelta
      obtain ⟨q, hql, rfl⟩ := List.mem_map.mp hdelta
      obtain ⟨d, hd, rfl⟩ := hl q hql
      simpa [Pattern.rename_comp] using hd
    · have hp' := hp.renameEquiv e.symm
      simpa [Pattern.rename, rename_conj, Pattern.rename_comp] using hp'

/-- A source-faithful countably infinite variable type can be reduced to `Nat`. -/
theorem strongLocalCompleteness_iff_nat [DecidableEq Var] [Denumerable Var] :
    StrongLocalCompleteness S Var ↔ StrongLocalCompleteness S Nat := by
  exact strongLocalCompleteness_congr (Denumerable.eqv Var)

end MatchingLogic
