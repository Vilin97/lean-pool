/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
The technical witness-pushing lemma (Chen--Rosu TR, Lemma 80).

The source works modulo alpha equivalence and writes substitution as a total
operation.  Here `captureAvoidingSubst` is the proved raw-syntax realization of
that operation.  In particular, the public theorem below keeps the source's
free-variable freshness condition; it does not strengthen it to freshness from
bound names merely to fit the raw representation.
-/
import LeanPool.MatchingLogic.EntryIII.MCSAlpha

/-!
# MatchingLogic.EntryIII.WitnessPush
-/

namespace MatchingLogic

variable {S : Signature}

namespace Pattern

/-- Nested source notation `exists y1 ... exists yn, p`, with the
list order giving the outer-to-inner binder order. -/
def exList : List Nat -> Pattern S Nat -> Pattern S Nat
  | [], p => p
  | y :: ys, p => .ex y (exList ys p)

/-- A variable distinct from the replacement and absent from the source remains
absent after raw variable substitution. -/
theorem substVar_not_mem_FV_of_ne {x y z : Nat}
    {p : Pattern S Nat} (hzy : z ≠ y) (hzp : z ∉ FV p) :
    z ∉ FV (substVar x y p) := by
  induction p with
  | var a =>
      by_cases hax : a = x <;> simp_all [substVar]
  | bot => simp [substVar]
  | app sigma args ih =>
      simp only [substVar, FV_app, Set.mem_iUnion, not_exists] at hzp ⊢
      exact fun i => ih i (hzp i)
  | imp p q ihp ihq =>
      simp only [substVar, FV_imp, Set.mem_union, not_or] at hzp ⊢
      exact ⟨ihp hzp.1, ihq hzp.2⟩
  | ex a p ih =>
      by_cases hax : a = x
      · simpa [substVar, hax] using hzp
      · simp only [substVar, ite_eq_right hax]
        by_cases hza : z = a
        · simp [FV_ex, hza]
        · have hzbody : z ∉ FV p := by
            simpa [FV_ex, hza] using hzp
          simpa [FV_ex, hza] using ih hzbody

/-- Raw substitution commutes with a list of existential binders when its
source is distinct from every binder. -/
theorem substVar_exList {a b : Nat} (ys : List Nat) (p : Pattern S Nat)
    (ha : ∀ y ∈ ys, a ≠ y) :
    substVar a b (exList ys p) = exList ys (substVar a b p) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
      have hay : a ≠ y := ha y (by simp)
      simp only [exList, substVar, ite_eq_right (Ne.symm hay)]
      rw [ih (fun u hu => ha u (by simp [hu]))]

private theorem avoidBinder_not_mem_FV {y z : Nat} {p : Pattern S Nat}
    (hzp : z ∉ FV p) : z ∉ FV (avoidBinder y p) := by
  induction p with
  | var a => simpa [avoidBinder] using hzp
  | bot => simp [avoidBinder]
  | app sigma args ih =>
      simp only [avoidBinder, FV_app, Set.mem_iUnion, not_exists] at hzp ⊢
      exact fun i => ih i (hzp i)
  | imp p q ihp ihq =>
      simp only [avoidBinder, FV_imp, Set.mem_union, not_or] at hzp ⊢
      exact ⟨ihp hzp.1, ihq hzp.2⟩
  | ex a p ih =>
      simp only [avoidBinder]
      split
      · rename_i hay
        subst a
        let q := avoidBinder y p
        let w := (Pattern.ex y q).fresh
        have hwy : w ≠ y := by
          intro h
          apply (Pattern.ex y q).fresh_not_mem_allVars
          simp [w, h, Pattern.allVars]
        by_cases hzw : z = w
        · intro hzmem
          exact hzmem.2 hzw
        · by_cases hzy : z = y
          · subst z
            intro hzmem
            exact (substVar_source_not_mem_FV q (Ne.symm hwy)) hzmem.1
          · have hzbody : z ∉ FV p := by
              simpa [FV_ex, hzy] using hzp
            have hzq : z ∉ FV q := ih hzbody
            intro hzmem
            exact (substVar_not_mem_FV_of_ne (x := y) (y := w) hzw hzq) hzmem.1
      · rename_i hay
        by_cases hza : z = a
        · simp [FV_ex, hza]
        · have hzbody : z ∉ FV p := by
            simpa [FV_ex, hza] using hzp
          simpa [FV_ex, hza] using ih hzbody

private theorem not_mem_allVars_of_not_mem_FV_of_avoidsBinder {y : Nat}
    {p : Pattern S Nat} (hfree : y ∉ FV p) (havoid : AvoidsBinder y p) :
    y ∉ p.allVars := by
  induction p with
  | var z => simpa [allVars] using hfree
  | bot => simp [allVars]
  | app sigma args ih =>
      simp only [FV_app, Set.mem_iUnion, not_exists] at hfree
      simp only [allVars, Finset.mem_biUnion, Finset.mem_univ, true_and,
        not_exists]
      exact fun i => ih i (hfree i) (havoid i)
  | imp p q ihp ihq =>
      simp only [FV_imp, Set.mem_union, not_or] at hfree
      simp only [allVars, Finset.mem_union, not_or]
      exact ⟨ihp hfree.1 havoid.1, ihq hfree.2 havoid.2⟩
  | ex z p ih =>
      have hyz : y ≠ z := Ne.symm havoid.1
      have hybody : y ∉ FV p := by
        simpa [FV_ex, hyz] using hfree
      simp only [allVars, Finset.mem_insert, not_or]
      exact ⟨hyz, ih hybody havoid.2⟩

/-- A name distinct from the replacement and absent free from the source stays
absent free after total capture-avoiding substitution. -/
theorem captureAvoidingSubst_not_mem_FV_of_ne {x y z : Nat}
    {p : Pattern S Nat} (hzy : z ≠ y) (hzp : z ∉ FV p) :
    z ∉ FV (captureAvoidingSubst x y p) := by
  exact substVar_not_mem_FV_of_ne hzy (avoidBinder_not_mem_FV hzp)

end Pattern

/-- The source's alpha-renaming fact with its actual side condition: `y` need
only be absent from the free variables of `p`. -/
theorem Provable.exists_captureAvoidingSubst {Gamma : Set (Pattern S Nat)}
    {x y : Nat} {p : Pattern S Nat} (hy : y ∉ FV p) :
    Provable Gamma (.imp (.ex x p)
      (.ex y (Pattern.captureAvoidingSubst x y p))) := by
  let p' := Pattern.avoidBinder y p
  have hfree : y ∉ FV p' := Pattern.avoidBinder_not_mem_FV hy
  have hall : y ∉ p'.allVars :=
    Pattern.not_mem_allVars_of_not_mem_FV_of_avoidsBinder hfree
      (Pattern.avoidBinder_avoids y p)
  have halpha : Pattern.AlphaEq (.ex x p)
      (.ex y (substVar x y p')) :=
    (Pattern.AlphaEq.ex x (Pattern.avoidBinder_alphaEq y p)).trans
      (Pattern.AlphaEq.alphaEx hall)
  simpa [Pattern.captureAvoidingSubst, p'] using halpha.forward Gamma

private theorem taut_imp_of :
    PForm.Taut (.imp (.atom 0) (.imp (.atom 1) (.atom 0))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

private theorem taut_false_imp :
    PForm.Taut
      (.imp (.imp (.atom 0) .bot) (.imp (.atom 0) (.atom 1))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

private theorem taut_choice :
    PForm.Taut
      (.imp (.imp (.atom 1) (.atom 2))
        (.imp (.imp (.imp (.atom 0) .bot) (.atom 2))
          (.imp (.imp (.atom 0) (.atom 1)) (.atom 2)))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
    simp [PForm.eval, h0, h1, h2]

/-- Predicate-logic choice in the exact form needed by Lemma 80.  Nonemptiness
is supplied proof-theoretically by existential introduction. -/
theorem Provable.imp_exists_to_exists_imp {Gamma : Set (Pattern S Nat)}
    {y : Nat} {a q : Pattern S Nat} :
    Provable Gamma (.imp (.imp a (.ex y q)) (.ex y (.imp a q))) := by
  let e : Pattern S Nat := .ex y q
  let r : Pattern S Nat := .ex y (.imp a q)
  have hq : Provable Gamma (.imp q (.imp a q)) := by
    simpa [PForm.subst] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n => if n = 0 then q else a) taut_imp_of)
  have her : Provable Gamma (.imp e r) := by
    simpa [e, r] using Provable.ex_mono hq
  have hna : Provable Gamma (.imp (Pattern.nt a) (.imp a q)) := by
    simpa [PForm.subst, Pattern.nt] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n => if n = 0 then a else q) taut_false_imp)
  have hir : Provable Gamma (.imp (.imp a q) r) := by
    simpa [r, Pattern.substVar_self] using
      (Provable.exQuant (Γ := Gamma)
        (Pattern.captureFree_self y (.imp a q)))
  have hnar : Provable Gamma (.imp (Pattern.nt a) r) := hna.imp_trans hir
  have ht : Provable Gamma
      (.imp (.imp e r)
        (.imp (.imp (Pattern.nt a) r) (.imp (.imp a e) r))) := by
    simpa [PForm.subst, Pattern.nt] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n => if n = 0 then a else if n = 1 then e else r)
        taut_choice)
  exact .mp hnar (.mp her ht)

private theorem taut_right_conj :
    PForm.Taut (.imp (.atom 0)
      (.imp
        (.imp (.imp (.atom 1) (.imp (.atom 2) .bot)) .bot)
        (.imp (.imp (.atom 1) (.imp (.atom 0) .bot)) .bot))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
    simp [PForm.eval, h0, h1, h2]

private theorem taut_nested_trans :
    PForm.Taut
      (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2)))
        (.imp (.imp (.atom 2) (.atom 3))
          (.imp (.atom 0) (.imp (.atom 1) (.atom 3))))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
    cases h3 : v 3 <;> simp [PForm.eval, h0, h1, h2, h3]

private theorem taut_apply_curried :
    PForm.Taut
      (.imp (.imp (.atom 0) (.atom 1))
        (.imp (.imp (.atom 1) (.imp (.atom 0) (.atom 2)))
          (.imp (.atom 0) (.atom 2)))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
    simp [PForm.eval, h0, h1, h2]

/-- Move an existential through a conjunction whose other conjunct is fresh. -/
theorem Provable.and_exists {Gamma : Set (Pattern S Nat)} {y : Nat}
    {p q : Pattern S Nat} (hy : y ∉ FV p) :
    Provable Gamma (.imp (Pattern.and p (.ex y q))
      (.ex y (Pattern.and p q))) := by
  let b : Pattern S Nat := Pattern.and p (.ex y q)
  let c : Pattern S Nat := Pattern.and p q
  let r : Pattern S Nat := .ex y c
  have hqbc : Provable Gamma (.imp q (.imp b c)) := by
    simpa [PForm.subst, Pattern.and, Pattern.nt, b, c] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n => if n = 0 then q else if n = 1 then p else .ex y q)
        taut_right_conj)
  have hcr : Provable Gamma (.imp c r) := by
    simpa [r, Pattern.substVar_self] using
      (Provable.exQuant (Γ := Gamma) (Pattern.captureFree_self y c))
  have hqbr : Provable Gamma (.imp q (.imp b r)) := by
    have ht : Provable Gamma
        (.imp (.imp q (.imp b c))
          (.imp (.imp c r) (.imp q (.imp b r)))) := by
      simpa [PForm.subst] using
        (Provable.taut (Γ := Gamma)
          (θ := fun n =>
            if n = 0 then q else if n = 1 then b else if n = 2 then c else r)
          taut_nested_trans)
    exact .mp hcr (.mp hqbc ht)
  have hebr : Provable Gamma (.imp (.ex y q) (.imp b r)) := by
    exact .exGen hqbr (by
      simp [b, r, c, Pattern.and, Pattern.nt, hy])
  have hbe : Provable Gamma (.imp b (.ex y q)) := by
    simpa [b] using Provable.and_elim_right Gamma p (.ex y q)
  have ht : Provable Gamma
      (.imp (.imp b (.ex y q))
        (.imp (.imp (.ex y q) (.imp b r)) (.imp b r))) := by
    simpa [PForm.subst] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n => if n = 0 then b else if n = 1 then .ex y q else r)
        taut_apply_curried)
  simpa [b, r, c] using Provable.mp hebr (Provable.mp hbe ht)

private theorem taut_and_with :
    PForm.Taut
      (.imp (.atom 0)
        (.imp (.atom 1)
          (.imp (.imp (.atom 1) (.imp (.atom 0) .bot)) .bot))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

/-- One argument of Lemma 80, before application-context propagation. -/
theorem Provable.witnessPushArg {Gamma : Set (Pattern S Nat)}
    {x y : Nat} {phi Phi : Pattern S Nat}
    (hyphi : y ∉ FV phi) (hyPhi : y ∉ FV Phi) :
    Provable Gamma (.imp Phi
      (.ex y (Pattern.and Phi
        (.imp (.ex x phi) (Pattern.captureAvoidingSubst x y phi))))) := by
  let e : Pattern S Nat := .ex x phi
  let q : Pattern S Nat := Pattern.captureAvoidingSubst x y phi
  let r : Pattern S Nat := .ex y (.imp e q)
  have heq : Provable Gamma (.imp e (.ex y q)) := by
    simpa [e, q] using
      (Provable.exists_captureAvoidingSubst (Gamma := Gamma) hyphi)
  have her : Provable Gamma (.imp (.imp e (.ex y q)) r) := by
    exact Provable.imp_exists_to_exists_imp
  have hr : Provable Gamma r := .mp heq her
  have hPhi : Provable Gamma (.imp Phi (Pattern.and Phi r)) := by
    have ht : Provable Gamma
        (.imp r (.imp Phi (Pattern.and Phi r))) := by
      simpa [PForm.subst, Pattern.and, Pattern.nt] using
        (Provable.taut (Γ := Gamma)
          (θ := fun n => if n = 0 then r else Phi) taut_and_with)
    exact .mp hr ht
  exact hPhi.imp_trans (by
    simpa [r, e, q] using
      (Provable.and_exists (Gamma := Gamma) (y := y)
        (p := Phi) (q := .imp e q) hyPhi))

namespace Pattern

private def exOn {n : Nat} (is : List (Fin n)) (y : Fin n -> Nat)
    (body : Fin n -> Pattern S Nat) : Fin n -> Pattern S Nat :=
  fun i => if i ∈ is then .ex (y i) (body i) else body i

end Pattern

private theorem Provable.app_exists_list_aux {Gamma : Set (Pattern S Nat)}
    {sigma : S.Sym} (is : List (Fin (S.arity sigma)))
    (y : Fin (S.arity sigma) -> Nat)
    (body : Fin (S.arity sigma) -> Pattern S Nat)
    (hnodup : is.Nodup)
    (hfresh : forall i j, i ≠ j -> y i ∉ FV (body j)) :
    Provable Gamma (.imp
      (.app sigma (Pattern.exOn is y body))
      (Pattern.exList (is.map y) (.app sigma body))) := by
  induction is with
  | nil =>
      have heq : Pattern.exOn [] y body = body := by
        funext i
        simp [Pattern.exOn]
      simpa [heq, Pattern.exList] using
        (Provable.imp_refl Gamma (.app sigma body))
  | cons i is ih =>
      have hi : i ∉ is := (List.nodup_cons.mp hnodup).1
      have htail : is.Nodup := (List.nodup_cons.mp hnodup).2
      have hside : forall j, j ≠ i ->
          y i ∉ FV (Pattern.exOn is y body j) := by
        intro j hji
        by_cases hj : j ∈ is
        · rw [Pattern.exOn, ite_eq_left hj]
          intro hmem
          by_cases hyij : y i = y j
          · exact hmem.2 hyij
          · exact hfresh i j (Ne.symm hji) hmem.1
        · simpa [Pattern.exOn, hj] using hfresh i j (Ne.symm hji)
      have hprop := Provable.propEx (Γ := Gamma) (σ := sigma) (i := i)
        (args := Pattern.exOn is y body) (x := y i) (φ := body i) hside
      have hstep : Provable Gamma
          (.imp (.app sigma (Pattern.exOn (i :: is) y body))
            (.ex (y i) (.app sigma (Pattern.exOn is y body)))) := by
        have hleft :
            Function.update (Pattern.exOn is y body) i (.ex (y i) (body i)) =
              Pattern.exOn (i :: is) y body := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [Pattern.exOn]
          · simp [Pattern.exOn, hji]
        have hright :
            Function.update (Pattern.exOn is y body) i (body i) =
              Pattern.exOn is y body := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [Pattern.exOn, hi]
          · simp [hji]
        simpa only [hleft, hright] using hprop
      have hrec := ih htail
      exact hstep.imp_trans (by
        simpa [Pattern.exList] using Provable.ex_mono hrec)

/-- Simultaneously pull a finite tuple of existential arguments out of a
symbol application.  Pairwise freshness is exactly the side condition of
Propagation of Existential. -/
theorem Provable.app_exists_list {Gamma : Set (Pattern S Nat)}
    {sigma : S.Sym} (y : Fin (S.arity sigma) -> Nat)
    (body : Fin (S.arity sigma) -> Pattern S Nat)
    (hfresh : forall i j, i ≠ j -> y i ∉ FV (body j)) :
    Provable Gamma (.imp
      (.app sigma (fun i => .ex (y i) (body i)))
      (Pattern.exList (List.ofFn y) (.app sigma body))) := by
  have hn : (List.ofFn (fun i : Fin (S.arity sigma) => i)).Nodup := by
    rw [List.nodup_ofFn]
    exact Function.injective_id
  have h := Provable.app_exists_list_aux (Gamma := Gamma) (sigma := sigma)
    (List.ofFn (fun i : Fin (S.arity sigma) => i)) y body hn hfresh
  have hexOn :
      Pattern.exOn (List.ofFn (fun i : Fin (S.arity sigma) => i)) y body =
        (fun i => .ex (y i) (body i)) := by
    funext i
    rw [Pattern.exOn, ite_eq_left (List.mem_ofFn.mpr ⟨i, rfl⟩)]
  simpa [hexOn, List.map_ofFn, Function.comp_def] using h

/-- Technical witness-pushing lemma, Chen--Rosu TR Lemma 80, for every finite
arity (including zero).  The hypotheses say that the witnesses are pairwise
distinct and do not occur free in `phi` or in any original argument. -/
theorem Provable.witnessPush {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (phi : Pattern S Nat)
    (x : Nat) (y : Fin (S.arity sigma) -> Nat)
    (hyinj : Function.Injective y)
    (hyphi : forall i, y i ∉ FV phi)
    (hyPhi : forall i j, y i ∉ FV (Phi j)) :
    Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma Phi)
        (Pattern.exList (List.ofFn y)
          (.app sigma (fun i => Pattern.and (Phi i)
            (.imp (.ex x phi)
              (Pattern.captureAvoidingSubst x (y i) phi)))))) := by
  let body : Fin (S.arity sigma) -> Pattern S Nat := fun i =>
    Pattern.and (Phi i)
      (.imp (.ex x phi) (Pattern.captureAvoidingSubst x (y i) phi))
  have hargs : forall i, Provable (∅ : Set (Pattern S Nat))
      (.imp (Phi i) (.ex (y i) (body i))) := by
    intro i
    simpa [body] using
      (Provable.witnessPushArg (Gamma := (∅ : Set (Pattern S Nat)))
        (x := x) (y := y i) (phi := phi) (Phi := Phi i)
        (hyphi i) (hyPhi i i))
  have happ : Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma Phi) (.app sigma (fun i => .ex (y i) (body i)))) :=
    Provable.app_mono hargs
  have hfresh : forall i j, i ≠ j -> y i ∉ FV (body j) := by
    intro i j hij
    have hyne : y i ≠ y j := hyinj.ne hij
    have hca : y i ∉ FV (Pattern.captureAvoidingSubst x (y j) phi) :=
      Pattern.captureAvoidingSubst_not_mem_FV_of_ne hyne (hyphi i)
    simp [body, Pattern.and, Pattern.nt, hyPhi i j, hyphi i, hca]
  exact happ.imp_trans (by
    simpa [body] using
      (Provable.app_exists_list (Gamma := (∅ : Set (Pattern S Nat)))
        (sigma := sigma) y body hfresh))

end MatchingLogic
