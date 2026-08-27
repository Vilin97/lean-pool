/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Finite-signature restriction for entry point (iii).

The source proof reduces a finite collection of patterns to the signature made
of precisely the symbols that occur in them.  This file makes that reduction
explicit for the raw named syntax used by the base development, then shows that
a derivation over the finite sub-signature can be replayed over the ambient
signature.
-/
import LeanPool.MatchingLogic.EntryIII.SymbolSupport
import Mathlib.Logic.Equiv.List

/-!
# MatchingLogic.EntryIII.SignatureRestriction
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

namespace Signature

/-- The sub-signature containing exactly the symbols in `F`. -/
def restrict (F : Finset S.Sym) : Signature where
  Sym := {sigma : S.Sym // sigma ∈ F}
  arity sigma := S.arity sigma.1

end Signature

namespace Pattern

/-- Regard a pattern over a finite sub-signature as a pattern over `S`. -/
def liftSignature [DecidableEq S.Sym] (F : Finset S.Sym) :
    Pattern (S.restrict F) Var → Pattern S Var
  | .var x => .var x
  | .app sigma args => .app sigma.1 (fun i => (args i).liftSignature F)
  | .imp phi psi => .imp (phi.liftSignature F) (psi.liftSignature F)
  | .bot => .bot
  | .ex x phi => .ex x (phi.liftSignature F)

/-- Restrict a pattern whose symbol support lies in `F` to the sub-signature. -/
def restrictSignature [DecidableEq S.Sym] (F : Finset S.Sym) :
    (p : Pattern S Var) → p.symbolSupport ⊆ F → Pattern (S.restrict F) Var
  | .var x, _ => .var x
  | .bot, _ => .bot
  | .app sigma args, h =>
      .app ⟨sigma, h (head_mem_symbolSupport sigma args)⟩
        (fun i => (args i).restrictSignature F
          (fun _ htau => h (argument_symbolSupport_subset sigma args i htau)))
  | .imp phi psi, h =>
      .imp (phi.restrictSignature F (fun _ htau => h (by
        simp [symbolSupport, htau])))
        (psi.restrictSignature F (fun _ htau => h (by
          simp [symbolSupport, htau])))
  | .ex x phi, h => .ex x (phi.restrictSignature F h)

omit [DecidableEq Var] in
/-- Lifting a restricted pattern recovers the original ambient pattern. -/
theorem lift_restrictSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    (p : Pattern S Var) (h : p.symbolSupport ⊆ F) :
    (p.restrictSignature F h).liftSignature F = p := by
  induction p with
  | var x => rfl
  | bot => rfl
  | app sigma args ih =>
      simp only [restrictSignature, liftSignature]
      congr
      funext i
      apply ih i
  | imp phi psi ihphi ihpsi =>
      simp only [restrictSignature, liftSignature]
      congr
      · apply ihphi
      · apply ihpsi
  | ex x phi ih =>
      simp only [restrictSignature, liftSignature]
      congr
      apply ih

/-- Lifting commutes with the raw variable-for-variable substitution. -/
theorem liftSignature_substVar [DecidableEq S.Sym] (F : Finset S.Sym)
    (x y : Var) (p : Pattern (S.restrict F) Var) :
    (substVar x y p).liftSignature F = substVar x y (p.liftSignature F) := by
  induction p with
  | var z =>
      by_cases hzx : z = x <;> simp [substVar, liftSignature, hzx]
  | app sigma args ih =>
      simp only [substVar, liftSignature]
      congr
      funext i
      exact ih i
  | imp phi psi ihphi ihpsi => simp [substVar, liftSignature, ihphi, ihpsi]
  | bot => rfl
  | ex z phi ih =>
      by_cases hzx : z = x
      · simp [substVar, liftSignature, hzx]
      · simp [substVar, liftSignature, hzx, ih]

omit [DecidableEq Var] in
/-- Free variables are unchanged by signature lifting. -/
theorem FV_liftSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    (p : Pattern (S.restrict F) Var) :
    FV (p.liftSignature F) = FV p := by
  induction p with
  | var x => rfl
  | bot => rfl
  | app sigma args ih =>
      change (⋃ i, FV ((args i).liftSignature F)) = ⋃ i, FV (args i)
      apply Set.iUnion_congr
      intro i
      exact ih i
  | imp phi psi ihphi ihpsi => simp [liftSignature, FV_imp, ihphi, ihpsi]
  | ex x phi ih => simp [liftSignature, FV_ex, ih]

omit [DecidableEq Var] in
/-- Capture-freedom is preserved when a pattern is lifted to a larger signature. -/
theorem captureFree_liftSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    {x y : Var} {p : Pattern (S.restrict F) Var} :
    CaptureFree x y p → CaptureFree x y (p.liftSignature F) := by
  intro h
  induction p generalizing x y with
  | var z => trivial
  | bot => trivial
  | app sigma args ih =>
      intro i
      exact ih i (h i)
  | imp phi psi ihphi ihpsi => exact ⟨ihphi h.1, ihpsi h.2⟩
  | ex z phi ih =>
      rcases h with hzx | hfree | ⟨hzy, hrec⟩
      · exact Or.inl hzx
      · exact Or.inr (Or.inl (by simpa [FV_liftSignature] using hfree))
      · exact Or.inr (Or.inr ⟨hzy, ih hrec⟩)

omit [DecidableEq Var] in
/-- Lifting commutes with replacing an argument of an application. -/
theorem liftSignature_update [DecidableEq S.Sym] (F : Finset S.Sym) {n : Nat}
    (args : Fin n → Pattern (S.restrict F) Var) (i : Fin n)
    (p : Pattern (S.restrict F) Var) :
    (fun j => (Function.update args i p j).liftSignature F) =
      Function.update (fun j => (args j).liftSignature F) i (p.liftSignature F) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

omit [DecidableEq Var] in
/-- The lifted form of an application with one replaced argument. -/
theorem liftSignature_app_update [DecidableEq S.Sym] (F : Finset S.Sym)
    (sigma : (S.restrict F).Sym) (args : Fin ((S.restrict F).arity sigma) →
      Pattern (S.restrict F) Var)
    (i : Fin ((S.restrict F).arity sigma)) (p : Pattern (S.restrict F) Var) :
    (Pattern.app sigma (Function.update args i p)).liftSignature F =
      Pattern.app sigma.1
        (Function.update (fun j => (args j).liftSignature F) i (p.liftSignature F)) := by
  simp only [liftSignature]
  congr
  exact liftSignature_update F args i p

end Pattern

omit [DecidableEq Var] in
/-- Lifting commutes with propositional-pattern substitution. -/
theorem PForm.subst_liftSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    (p : PForm) (theta : Nat → Pattern (S.restrict F) Var) :
    (p.subst theta).liftSignature F = p.subst (fun n => (theta n).liftSignature F) := by
  induction p with
  | atom n => rfl
  | bot => rfl
  | imp p q ihp ihq => simp [PForm.subst, Pattern.liftSignature, ihp, ihq]

namespace AppCtx

/-- Regard an application context over a finite sub-signature as one over `S`. -/
def liftSignature [DecidableEq S.Sym] (F : Finset S.Sym) :
    AppCtx (S.restrict F) Var → AppCtx S Var
  | .hole => .hole
  | .node sigma i args C =>
      .node sigma.1 i (fun j => (args j).liftSignature F) (C.liftSignature F)

/- Lifting commutes with plugging an application context. -/
omit [DecidableEq Var] in
theorem plug_liftSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    (C : AppCtx (S.restrict F) Var) (p : Pattern (S.restrict F) Var) :
    (C.plug p).liftSignature F = (C.liftSignature F).plug (p.liftSignature F) := by
  induction C with
  | hole => rfl
  | node sigma i args C ih =>
      have hupdate := Pattern.liftSignature_update F args i (C.plug p)
      rw [ih] at hupdate
      exact congrArg (Pattern.app sigma.1) hupdate

end AppCtx

namespace Pattern

/-- A natural-number serialization retaining every application argument. -/
noncomputable def signatureNatCode {T : Signature} [Encodable T.Sym] :
    Pattern T Nat → Nat
  | .var x => Nat.pair 0 x
  | .app sigma args => Nat.pair 1 (Nat.pair (Encodable.encode sigma)
      (Encodable.encode (List.ofFn fun i => (args i).signatureNatCode)))
  | .imp phi psi => Nat.pair 2 (Nat.pair phi.signatureNatCode psi.signatureNatCode)
  | .bot => Nat.pair 3 0
  | .ex x phi => Nat.pair 4 (Nat.pair x phi.signatureNatCode)

private def signatureNatTag : Pattern T Nat → Nat
  | .var _ => 0
  | .app _ _ => 1
  | .imp _ _ => 2
  | .bot => 3
  | .ex _ _ => 4

private theorem signatureNatTag_eq_of_code_eq {T : Signature} [Encodable T.Sym]
    {p q : Pattern T Nat} (h : p.signatureNatCode = q.signatureNatCode) :
    signatureNatTag p = signatureNatTag q := by
  have h' := congrArg (fun n => (Nat.unpair n).1) h
  cases p <;> cases q <;>
    simp [signatureNatTag, signatureNatCode] at h' ⊢

/-- The natural serialization is injective whenever the symbol type is encodable. -/
theorem signatureNatCode_injective {T : Signature} [Encodable T.Sym] :
    Function.Injective (@signatureNatCode T _) := by
  intro p
  induction p with
  | var x =>
      intro q h
      have htag := signatureNatTag_eq_of_code_eq h
      cases q
      case var y =>
        exact congrArg Pattern.var (Nat.pair_eq_pair.mp h).2
      all_goals simp [signatureNatTag] at htag
  | bot =>
      intro q h
      have htag := signatureNatTag_eq_of_code_eq h
      cases q
      case bot => rfl
      all_goals simp [signatureNatTag] at htag
  | imp p q ihp ihq =>
      intro r h
      have htag := signatureNatTag_eq_of_code_eq h
      cases r
      case imp p' q' =>
        have hpq := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2
        cases ihp hpq.1
        cases ihq hpq.2
        rfl
      all_goals simp [signatureNatTag] at htag
  | ex x p ih =>
      intro q h
      have htag := signatureNatTag_eq_of_code_eq h
      cases q
      case ex y q =>
        have hxp := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2
        cases hxp.1
        cases ih hxp.2
        rfl
      all_goals simp [signatureNatTag] at htag
  | app sigma args ih =>
      intro q h
      have htag := signatureNatTag_eq_of_code_eq h
      cases q
      case app tau bs =>
        have hsargs := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2
        have hst : sigma = tau := Encodable.encode_injective hsargs.1
        subst tau
        have hargs : List.ofFn (fun i => (args i).signatureNatCode) =
            List.ofFn (fun i => (bs i).signatureNatCode) :=
          Encodable.encode_injective hsargs.2
        congr
        funext i
        apply ih i
        exact congrFun (List.ofFn_injective hargs) i
      all_goals simp [signatureNatTag] at htag

end Pattern

/-- A finite signature yields a countable type of natural-variable patterns. -/
theorem restrictedPatternNatCountable
    (F : Finset S.Sym) : Countable (Pattern (S.restrict F) Nat) := by
  classical
  let : Fintype (S.restrict F).Sym := by
    unfold Signature.restrict
    infer_instance
  let : Encodable (S.restrict F).Sym :=
    Encodable.ofEquiv (Fin (Fintype.card (S.restrict F).Sym))
      (Fintype.equivFin (S.restrict F).Sym)
  exact ⟨Pattern.signatureNatCode, Pattern.signatureNatCode_injective⟩

/-- A derivation over a finite sub-signature can be replayed over `S`. -/
theorem Provable.liftSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    {Gamma : Set (Pattern (S.restrict F) Var)} {phi : Pattern (S.restrict F) Var}
    (h : Provable Gamma phi) :
    Provable (Pattern.liftSignature F '' Gamma) (phi.liftSignature F) := by
  induction h with
  | hyp hphi => exact .hyp ⟨_, hphi, rfl⟩
  | taut hp =>
      rw [PForm.subst_liftSignature]
      exact .taut hp
  | mp hphi himp ihphi ihimp => exact .mp ihphi ihimp
  | exQuant hfree =>
      simpa [Pattern.liftSignature, Pattern.liftSignature_substVar] using
        (Provable.exQuant (S := S) (Var := Var) (Γ := Pattern.liftSignature F '' Gamma)
          (Pattern.captureFree_liftSignature F hfree))
  | exGen himp hfree ih =>
      apply Provable.exGen ih
      intro hmem
      apply hfree
      simpa [Pattern.FV_liftSignature] using hmem
  | @propBot sigma i args =>
      have h := Provable.propBot (S := S) (Var := Var)
        (Γ := Pattern.liftSignature F '' Gamma)
        (σ := sigma.1) (i := i) (args := fun j => (args j).liftSignature F)
      change Provable (Pattern.liftSignature F '' Gamma)
        (.imp ((Pattern.app sigma (Function.update args i .bot)).liftSignature F) .bot)
      rw [Pattern.liftSignature_app_update]
      exact h
  | @propOr sigma i args phi₁ phi₂ =>
      have h := Provable.propOr (S := S) (Var := Var)
        (Γ := Pattern.liftSignature F '' Gamma)
        (σ := sigma.1) (i := i) (args := fun j => (args j).liftSignature F)
        (φ₁ := phi₁.liftSignature F) (φ₂ := phi₂.liftSignature F)
      change Provable (Pattern.liftSignature F '' Gamma)
        (.imp ((Pattern.app sigma (Function.update args i (Pattern.or phi₁ phi₂))).liftSignature F)
          (Pattern.or ((Pattern.app sigma (Function.update args i phi₁)).liftSignature F)
            ((Pattern.app sigma (Function.update args i phi₂)).liftSignature F)))
      rw [Pattern.liftSignature_app_update, Pattern.liftSignature_app_update,
        Pattern.liftSignature_app_update]
      rw [show (Pattern.or phi₁ phi₂).liftSignature F =
        Pattern.or (phi₁.liftSignature F) (phi₂.liftSignature F) by rfl]
      exact h
  | @propEx sigma i args x phi hfree =>
      have hfree' : ∀ j, j ≠ i → x ∉ FV ((args j).liftSignature F) := by
        intro j hji hmem
        apply hfree j hji
        simpa [Pattern.FV_liftSignature] using hmem
      have h := Provable.propEx (S := S) (Var := Var)
        (Γ := Pattern.liftSignature F '' Gamma)
        (σ := sigma.1) (i := i) (args := fun j => (args j).liftSignature F)
        (x := x) (φ := phi.liftSignature F) hfree'
      change Provable (Pattern.liftSignature F '' Gamma)
        (.imp ((Pattern.app sigma (Function.update args i (.ex x phi))).liftSignature F)
          (.ex x ((Pattern.app sigma (Function.update args i phi)).liftSignature F)))
      rw [Pattern.liftSignature_app_update, Pattern.liftSignature_app_update]
      exact h
  | @framing sigma i args phi₁ phi₂ himp ih =>
      have h := Provable.framing (S := S) (Var := Var)
        (Γ := Pattern.liftSignature F '' Gamma)
        (σ := sigma.1) (i := i) (args := fun j => (args j).liftSignature F) ih
      change Provable (Pattern.liftSignature F '' Gamma)
        (.imp ((Pattern.app sigma (Function.update args i phi₁)).liftSignature F)
          ((Pattern.app sigma (Function.update args i phi₂)).liftSignature F))
      rw [Pattern.liftSignature_app_update, Pattern.liftSignature_app_update]
      exact h
  | @existence x =>
      simpa [Pattern.liftSignature] using
        (Provable.existence (S := S) (Var := Var)
          (Γ := Pattern.liftSignature F '' Gamma) (x := x))
  | @singleton x phi C₁ C₂ =>
      simpa [AppCtx.plug_liftSignature, Pattern.liftSignature, Pattern.and, Pattern.nt] using
        (Provable.singleton (S := S) (Var := Var)
          (Γ := Pattern.liftSignature F '' Gamma) (x := x)
          (φ := phi.liftSignature F) (C₁.liftSignature F) (C₂.liftSignature F))

end MatchingLogic
