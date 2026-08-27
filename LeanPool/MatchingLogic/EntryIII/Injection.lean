/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Forward transport along injective variable embeddings.

The extension construction in the source embeds the original variable set in
a larger one before adding Henkin witnesses.  This module isolates the safe
forward half of that move for the verified raw named calculus.
-/
import LeanPool.MatchingLogic.EntryIII.Renaming

/-!
# MatchingLogic.EntryIII.Injection
-/

namespace MatchingLogic

variable {S : Signature} {Var Var' : Type}

namespace Pattern

/-- Free-variable membership is reflected at an embedded variable name. -/
theorem mem_FV_rename_injective
    (f : Var → Var') (hf : Function.Injective f) (p : Pattern S Var) (x : Var) :
    f x ∈ FV (p.rename f) ↔ x ∈ FV p := by
  classical
  induction p with
  | var y => simp [Pattern.rename, hf.eq_iff]
  | bot => simp [Pattern.rename]
  | app sigma args ih =>
      simp only [Pattern.rename, FV_app, Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (ih i).mp hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, (ih i).mpr hi⟩
  | imp phi psi ihphi ihpsi =>
      simp [Pattern.rename, ihphi, ihpsi]
  | ex y phi ih =>
      simp only [Pattern.rename, FV_ex, Set.mem_sdiff, Set.mem_singleton_iff, ih]
      exact and_congr Iff.rfl (not_congr hf.eq_iff)

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
      simp only [substVar, Pattern.rename]
      congr
      funext i
      exact ih i
  | imp phi psi ihphi ihpsi =>
      simp [substVar, Pattern.rename, ihphi, ihpsi]
  | bot => rfl
  | ex z phi ih =>
      by_cases hzx : z = x
      · simp [substVar, Pattern.rename, hzx]
      · simp [substVar, Pattern.rename, hzx, hf.eq_iff, ih]

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

end Pattern

/-- Plugging an application context commutes with an injective renaming. -/
theorem AppCtx.plug_rename_injective
    (f : Var → Var') (_hf : Function.Injective f)
    (C : AppCtx S Var) (p : Pattern S Var) :
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
      simpa [AppCtx.plug_rename_injective f hf, Pattern.rename,
        Pattern.and, Pattern.nt] using
        (Provable.singleton (Γ := Pattern.rename f '' Gamma) (x := f x)
          (φ := phi.rename f) (C1.rename f) (C2.rename f))

end MatchingLogic
