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

/-- Free-variable membership is reflected at an embedded variable name. -/
theorem mem_FV_rename_injective
    (f : Var → Var') (hf : Function.Injective f) (p : Pattern S Var) (x : Var) :
    f x ∈ FV (p.rename f) ↔ x ∈ FV p := by
  classical
  induction p with
  | var y => simp [rename, hf.eq_iff]
  | bot => simp [rename]
  | app sigma args ih =>
      simp only [rename, FV_app, Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (ih i).mp hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, (ih i).mpr hi⟩
  | imp phi psi ihphi ihpsi => simp [rename, ihphi, ihpsi]
  | ex y phi ih =>
      simp only [rename, FV_ex, Set.mem_sdiff, Set.mem_singleton_iff, ih]
      exact and_congr Iff.rfl (not_congr hf.eq_iff)

/-- Free-variable membership commutes with a bijective renaming. -/
theorem mem_FV_renameEquiv
    (e : Var ≃ Var') (p : Pattern S Var) (y : Var') :
    y ∈ FV (p.rename e) ↔ e.symm y ∈ FV p := by
  simpa using mem_FV_rename_injective e e.injective p (e.symm y)

/-- Variable substitution commutes with an injective renaming. -/
theorem substVar_rename_injective [DecidableEq Var] [DecidableEq Var']
    (f : Var → Var') (hf : Function.Injective f) (x y : Var) (p : Pattern S Var) :
    (substVar x y p).rename f = substVar (f x) (f y) (p.rename f) := by
  induction p with
  | var z =>
      by_cases hzx : z = x
      · simp [substVar, Pattern.rename, hzx]
      · simp [substVar, Pattern.rename, hzx, hf.eq_iff]
  | app sigma args ih =>
      simp only [substVar, rename]
      congr
      funext i
      exact ih i
  | imp phi psi ihphi ihpsi => simp [substVar, rename, ihphi, ihpsi]
  | bot => rfl
  | ex z phi ih =>
      by_cases hzx : z = x
      · simp [substVar, Pattern.rename, hzx]
      · simp [substVar, Pattern.rename, hzx, hf.eq_iff, ih]

/-- Variable-for-variable substitution commutes with a bijective renaming. -/
theorem substVar_renameEquiv [DecidableEq Var] [DecidableEq Var']
    (e : Var ≃ Var') (x y : Var) (p : Pattern S Var) :
    (substVar x y p).rename e = substVar (e x) (e y) (p.rename e) :=
  substVar_rename_injective e e.injective x y p

/-- Capture-freedom is preserved by an injective renaming. -/
theorem captureFree_rename_injective
    (f : Var → Var') (hf : Function.Injective f) {x y : Var} {p : Pattern S Var}
    (h : CaptureFree x y p) :
    CaptureFree (f x) (f y) (p.rename f) := by
  classical
  induction p generalizing x y with
  | var z => trivial
  | bot => trivial
  | app sigma args ih =>
      intro i
      exact ih i (h i)
  | imp phi psi ihphi ihpsi =>
      exact ⟨ihphi h.1, ihpsi h.2⟩
  | ex z phi ih =>
      rcases h with hzx | hfree | ⟨hzy, hrec⟩
      · exact Or.inl (congrArg f hzx)
      · apply Or.inr (Or.inl ?_)
        intro hmem
        exact hfree ((mem_FV_rename_injective f hf phi x).mp hmem)
      · exact Or.inr (Or.inr ⟨fun heq => hzy (hf heq), ih hrec⟩)

/-- A bijective renaming preserves the capture-freedom side condition. -/
theorem captureFree_renameEquiv
    (e : Var ≃ Var') {x y : Var} {p : Pattern S Var}
    (h : CaptureFree x y p) :
    CaptureFree (e x) (e y) (p.rename e) :=
  captureFree_rename_injective e e.injective h

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

/-- Plugging an application context commutes with a variable renaming. -/
theorem AppCtx.plug_rename_injective
    (f : Var → Var') (C : AppCtx S Var) (p : Pattern S Var) :
    (C.plug p).rename f = (C.rename f).plug (p.rename f) := by
  induction C with
  | hole => rfl
  | node sigma i args C ih =>
      simp only [AppCtx.plug, AppCtx.rename, Pattern.rename]
      congr
      funext j
      by_cases hji : j = i
      · subst j
        simpa using ih
      · simp [hji]

/-- Renaming commutes with plugging an application context. -/
theorem AppCtx.plug_renameEquiv
    (e : Var ≃ Var') (C : AppCtx S Var) (p : Pattern S Var) :
    (C.plug p).rename e = (C.rename e).plug (p.rename e) :=
  AppCtx.plug_rename_injective e C p

/-- Renaming distributes through finite conjunction. -/
theorem rename_conj (f : Var → Var') (l : List (Pattern S Var)) :
    (conj l).rename f = conj (l.map (Pattern.rename f)) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [conj, Pattern.and, Pattern.nt, Pattern.rename, ih]

/-- Denotation commutes with an injective variable embedding. -/
theorem Model.denote_renameInjective [DecidableEq Var] [DecidableEq Var']
    (M : Model S) (f : Var → Var') (hf : Function.Injective f)
    (rho : Var' → M.carrier)
    (p : Pattern S Var) :
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

/-- Denotation is unchanged by a bijective change of variable names. -/
theorem Model.denote_renameEquiv [DecidableEq Var] [DecidableEq Var']
    (M : Model S) (e : Var ≃ Var') (rho : Var' → M.carrier)
    (p : Pattern S Var) :
    M.denote rho (p.rename e) = M.denote (rho ∘ e) p :=
  M.denote_renameInjective e e.injective rho p

/-- Conjunctive denotation commutes with an injective variable embedding. -/
theorem Model.denoteSet_renameInjective [DecidableEq Var] [DecidableEq Var']
    (M : Model S) (f : Var → Var') (hf : Function.Injective f)
    (rho : Var' → M.carrier)
    (Delta : Set (Pattern S Var)) :
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

/-- Conjunctive denotation of a theory is unchanged by a bijective renaming. -/
theorem Model.denoteSet_renameEquiv [DecidableEq Var] [DecidableEq Var']
    (M : Model S) (e : Var ≃ Var') (rho : Var' → M.carrier)
    (Delta : Set (Pattern S Var)) :
    M.denoteSet rho (Pattern.rename e '' Delta) = M.denoteSet (rho ∘ e) Delta :=
  M.denoteSet_renameInjective e e.injective rho Delta

/-- Every raw derivation embeds into a larger variable type. -/
theorem Provable.renameInjective [DecidableEq Var] [DecidableEq Var']
    (f : Var → Var') (hf : Function.Injective f)
    {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (h : Provable Gamma phi) :
    Provable (Pattern.rename f '' Gamma) (phi.rename f) := by
  induction h with
  | hyp hphi => exact .hyp ⟨_, hphi, rfl⟩
  | taut hp =>
      rw [PForm.subst_rename]
      exact .taut hp
  | mp hphi himp ihphi ihimp => exact .mp ihphi ihimp
  | exQuant hfree =>
      simpa [Pattern.rename, Pattern.substVar_rename_injective f hf] using
        (Provable.exQuant (Γ := Pattern.rename f '' Gamma)
          (Pattern.captureFree_rename_injective f hf hfree))
  | exGen himp hfree ih =>
      apply Provable.exGen ih
      intro hmem
      exact hfree ((Pattern.mem_FV_rename_injective f hf _ _).mp hmem)
  | @propBot sigma i args =>
      simpa [Pattern.rename, Pattern.rename_update] using
        (Provable.propBot (Γ := Pattern.rename f '' Gamma)
          (σ := sigma) (i := i) (args := fun j => (args j).rename f))
  | @propOr sigma i args phi1 phi2 =>
      simpa [Pattern.rename, Pattern.or, Pattern.nt, Pattern.rename_update] using
        (Provable.propOr (Γ := Pattern.rename f '' Gamma)
          (σ := sigma) (i := i) (args := fun j => (args j).rename f)
          (φ₁ := phi1.rename f) (φ₂ := phi2.rename f))
  | @propEx sigma i args x phi hfree =>
      have hfree' : ∀ j, j ≠ i → f x ∉ FV ((args j).rename f) := by
        intro j hji hmem
        exact hfree j hji ((Pattern.mem_FV_rename_injective f hf _ _).mp hmem)
      simpa [Pattern.rename, Pattern.rename_update] using
        (Provable.propEx (Γ := Pattern.rename f '' Gamma)
          (σ := sigma) (i := i) (args := fun j => (args j).rename f)
          (x := f x) (φ := phi.rename f) hfree')
  | @framing sigma i args phi1 phi2 himp ih =>
      simpa [Pattern.rename, Pattern.rename_update] using
        (Provable.framing (Γ := Pattern.rename f '' Gamma)
          (σ := sigma) (i := i) (args := fun j => (args j).rename f) ih)
  | @existence x =>
      simpa [Pattern.rename] using
        (Provable.existence (Γ := Pattern.rename f '' Gamma) (x := f x))
  | @singleton x phi C1 C2 =>
      simpa [AppCtx.plug_rename_injective f, Pattern.rename,
        Pattern.and, Pattern.nt] using
        (Provable.singleton (Γ := Pattern.rename f '' Gamma) (x := f x)
          (φ := phi.rename f) (C1.rename f) (C2.rename f))

/-- Derivability is invariant under a bijective change of variable names. -/
theorem Provable.renameEquiv [DecidableEq Var] [DecidableEq Var']
    (e : Var ≃ Var') {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (h : Provable Gamma phi) :
    Provable (Pattern.rename e '' Gamma) (phi.rename e) :=
  h.renameInjective e e.injective

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

/-- Local consequence is invariant under a bijective change of variable names. -/
theorem localCons_renameEquiv [DecidableEq Var] [DecidableEq Var']
    (e : Var ≃ Var') {Delta : Set (Pattern S Var)} {phi : Pattern S Var} :
    LocalCons Delta phi ↔ LocalCons (Pattern.rename e '' Delta) (phi.rename e) :=
  localCons_renameInjective e e.injective

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
