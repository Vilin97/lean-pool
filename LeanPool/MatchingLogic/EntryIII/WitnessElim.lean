/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Repeated witness elimination for the raw named syntax used by entry point (iii).

The source silently computes modulo alpha equivalence.  Sequentially
instantiating the nested existentials produced by Lemma 80 therefore requires
an explicit normalization theorem for total capture-avoiding substitution.
-/
import LeanPool.MatchingLogic.EntryIII.WitnessPush
import LeanPool.MatchingLogic.EntryIII.FreshWitnessElim

/-!
# MatchingLogic.EntryIII.WitnessElim
-/

namespace MatchingLogic

variable {S : Signature}

private theorem taut_double_neg_intro :
    PForm.Taut (.imp (.atom 0) (.imp (.imp (.atom 0) .bot) .bot)) := by
  intro v
  cases h0 : v 0 <;> simp [PForm.eval, h0]

private theorem taut_double_neg_elim :
    PForm.Taut (.imp (.imp (.imp (.atom 0) .bot) .bot) (.atom 0)) := by
  intro v
  cases h0 : v 0 <;> simp [PForm.eval, h0]

/-- Empty-theory derivability is admissibly closed under total
capture-avoiding substitution. -/
theorem Provable.captureAvoidingSubst_theorem {r : Pattern S Nat}
    (h : Provable (∅ : Set (Pattern S Nat)) r) (x y : Nat) :
    Provable (∅ : Set (Pattern S Nat))
      (Pattern.captureAvoidingSubst x y r) := by
  let r' := Pattern.avoidBinder y r
  let q := substVar x y r'
  have hr' : Provable (∅ : Set (Pattern S Nat)) r' :=
    .mp h ((Pattern.avoidBinder_alphaEq y r).forward ∅)
  have hdni : Provable (∅ : Set (Pattern S Nat))
      (.imp r' (Pattern.nt (Pattern.nt r'))) := by
    simpa [PForm.subst] using
      (Provable.taut (Γ := (∅ : Set (Pattern S Nat)))
        (θ := fun _ => r') taut_double_neg_intro)
  have hdneg : Provable (∅ : Set (Pattern S Nat))
      (Pattern.nt (Pattern.nt r')) := .mp hr' hdni
  have hall : Provable (∅ : Set (Pattern S Nat))
      (Pattern.nt (.ex x (Pattern.nt r'))) := by
    exact .exGen hdneg (by simp)
  have hcf : CaptureFree x y (Pattern.nt r') := by
    exact ⟨(Pattern.avoidBinder_avoids y r).captureFree, trivial⟩
  have hex : Provable (∅ : Set (Pattern S Nat))
      (.imp (Pattern.nt q) (.ex x (Pattern.nt r'))) := by
    simpa [q, Pattern.nt, substVar] using
      (Provable.exQuant (Γ := (∅ : Set (Pattern S Nat))) hcf)
  have hbdn : Provable (∅ : Set (Pattern S Nat))
      (.imp (.ex x (Pattern.nt r'))
        (Pattern.nt (Pattern.nt (.ex x (Pattern.nt r'))))) := by
    simpa [PForm.subst, Pattern.nt] using
      (Provable.taut (Γ := (∅ : Set (Pattern S Nat)))
        (θ := fun _ => .ex x (Pattern.nt r')) taut_double_neg_intro)
  have hcontra : Provable (∅ : Set (Pattern S Nat))
      (.imp (Pattern.nt (.ex x (Pattern.nt r')))
        (Pattern.nt (Pattern.nt q))) := by
    exact (hex.imp_trans hbdn).swap_not
  have hdnq : Provable (∅ : Set (Pattern S Nat))
      (Pattern.nt (Pattern.nt q)) := .mp hall hcontra
  have hde : Provable (∅ : Set (Pattern S Nat))
      (.imp (Pattern.nt (Pattern.nt q)) q) := by
    simpa [PForm.subst, Pattern.nt] using
      (Provable.taut (Γ := (∅ : Set (Pattern S Nat)))
        (θ := fun _ => q) taut_double_neg_elim)
  simpa [Pattern.captureAvoidingSubst, r', q] using Provable.mp hdnq hde

/-- Total capture-avoiding substitution respects proof-theoretic alpha
equivalence. -/
theorem Pattern.AlphaEq.captureAvoidingSubst {p q : Pattern S Nat}
    (h : Pattern.AlphaEq p q) (x y : Nat) :
    Pattern.AlphaEq (Pattern.captureAvoidingSubst x y p)
      (Pattern.captureAvoidingSubst x y q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Gamma
    exact (Provable.captureAvoidingSubst_theorem (h.forward ∅) x y).weaken_empty
  · intro Gamma
    exact (Provable.captureAvoidingSubst_theorem (h.backward ∅) x y).weaken_empty
  · rw [Pattern.complexity_captureAvoidingSubst,
      Pattern.complexity_captureAvoidingSubst]
    exact h.complexity_eq

namespace Pattern

private def avoidTwo (y z : Nat) : Pattern S Nat -> Pattern S Nat
  | .var a => .var a
  | .bot => .bot
  | .app sigma args => .app sigma (fun i => avoidTwo y z (args i))
  | .imp p q => .imp (avoidTwo y z p) (avoidTwo y z q)
  | .ex a p =>
      let q := avoidTwo y z p
      if _h : a = y ∨ a = z then
        let w := (Pattern.imp (Pattern.var y)
          (Pattern.imp (Pattern.var z) (Pattern.ex a q))).fresh
        .ex w (substVar a w q)
      else .ex a q

private theorem avoidTwo_avoids (y z : Nat) (p : Pattern S Nat) :
    AvoidsBinder y (avoidTwo y z p) ∧ AvoidsBinder z (avoidTwo y z p) := by
  induction p with
  | var a => exact ⟨trivial, trivial⟩
  | bot => exact ⟨trivial, trivial⟩
  | app sigma args ih => exact ⟨fun i => (ih i).1, fun i => (ih i).2⟩
  | imp p q ihp ihq => exact ⟨⟨ihp.1, ihq.1⟩, ⟨ihp.2, ihq.2⟩⟩
  | ex a p ih =>
      simp only [avoidTwo]
      split
      · let q := avoidTwo y z p
        let w := (Pattern.imp (Pattern.var y)
          (Pattern.imp (Pattern.var z) (Pattern.ex a q))).fresh
        have hw0 := (Pattern.imp (Pattern.var y)
          (Pattern.imp (Pattern.var z) (Pattern.ex a q))).fresh_not_mem_allVars
        have hwy : w ≠ y := by
          intro h
          apply hw0
          simp [w, h, allVars]
        have hwz : w ≠ z := by
          intro h
          apply hw0
          simp [w, h, allVars]
        exact ⟨⟨hwy, ih.1.substVar⟩, ⟨hwz, ih.2.substVar⟩⟩
      · rename_i hnot
        exact ⟨⟨fun h => hnot (Or.inl h), ih.1⟩,
          ⟨fun h => hnot (Or.inr h), ih.2⟩⟩

private theorem avoidTwo_alphaEq (y z : Nat) (p : Pattern S Nat) :
    AlphaEq p (avoidTwo y z p) := by
  induction p with
  | var a => exact .refl _
  | bot => exact .refl _
  | app sigma args ih => exact .app ih
  | imp p q ihp ihq => exact .imp ihp ihq
  | ex a p ih =>
      simp only [avoidTwo]
      split
      · let q := avoidTwo y z p
        let w := (Pattern.imp (Pattern.var y)
          (Pattern.imp (Pattern.var z) (Pattern.ex a q))).fresh
        have hw0 := (Pattern.imp (Pattern.var y)
          (Pattern.imp (Pattern.var z) (Pattern.ex a q))).fresh_not_mem_allVars
        have hwq : w ∉ q.allVars := by
          intro h
          apply hw0
          simp [w, allVars, h]
        exact (AlphaEq.ex a ih).trans (AlphaEq.alphaEx hwq)
      · exact AlphaEq.ex a ih

private theorem substVar_not_mem_FV_of_ne {a b t : Nat}
    {p : Pattern S Nat} (htb : t ≠ b) (htp : t ∉ FV p) :
    t ∉ FV (substVar a b p) := by
  induction p with
  | var v => by_cases hva : v = a <;> simp_all [substVar]
  | bot => simp [substVar]
  | app sigma args ih =>
      simp only [substVar, FV_app, Set.mem_iUnion, not_exists] at htp ⊢
      exact fun i => ih i (htp i)
  | imp p q ihp ihq =>
      simp only [substVar, FV_imp, Set.mem_union, not_or] at htp ⊢
      exact ⟨ihp htp.1, ihq htp.2⟩
  | ex v p ih =>
      by_cases hva : v = a
      · simpa [substVar, hva] using htp
      · simp only [substVar, ite_eq_right hva]
        by_cases htv : t = v
        · simp [FV_ex, htv]
        · have htq : t ∉ FV p := by simpa [FV_ex, htv] using htp
          simpa [FV_ex, htv] using ih htq

private theorem substVar_eq_self_of_not_mem_FV {a b : Nat}
    {p : Pattern S Nat} (ha : a ∉ FV p) : substVar a b p = p := by
  induction p with
  | var v =>
      simp only [FV_var, Set.mem_singleton_iff] at ha
      simp [substVar, Ne.symm ha]
  | bot => rfl
  | app sigma args ih =>
      simp only [FV_app, Set.mem_iUnion, not_exists] at ha
      simp only [substVar]
      congr
      funext i
      exact ih i (ha i)
  | imp p q ihp ihq =>
      simp only [FV_imp, Set.mem_union, not_or] at ha
      simp [substVar, ihp ha.1, ihq ha.2]
  | ex v p ih =>
      by_cases hva : v = a
      · simp [substVar, hva]
      · have hap : a ∉ FV p := by
          intro hmem
          exact ha ⟨hmem, Ne.symm hva⟩
        simp [substVar, hva, ih hap]

private theorem avoidTwo_not_mem_FV {y z : Nat} {p : Pattern S Nat}
    (hy : y ∉ FV p) : y ∉ FV (avoidTwo y z p) := by
  induction p with
  | var a => simpa [avoidTwo] using hy
  | bot => simp [avoidTwo]
  | app sigma args ih =>
      simp only [FV_app, Set.mem_iUnion, not_exists] at hy
      simp only [avoidTwo, FV_app, Set.mem_iUnion, not_exists]
      exact fun i => ih i (hy i)
  | imp p q ihp ihq =>
      simp only [FV_imp, Set.mem_union, not_or] at hy
      simp only [avoidTwo, FV_imp, Set.mem_union, not_or]
      exact ⟨ihp hy.1, ihq hy.2⟩
  | ex a p ih =>
      simp only [avoidTwo]
      split
      · rename_i hrename
        let q := avoidTwo y z p
        let w := (Pattern.imp (Pattern.var y)
          (Pattern.imp (Pattern.var z) (Pattern.ex a q))).fresh
        have hw0 := (Pattern.imp (Pattern.var y)
          (Pattern.imp (Pattern.var z) (Pattern.ex a q))).fresh_not_mem_allVars
        have hwy : w ≠ y := by
          intro h
          apply hw0
          simp [w, h, allVars]
        by_cases hay : a = y
        · subst a
          intro hmem
          exact (substVar_source_not_mem_FV q (Ne.symm hwy)) hmem.1
        · have hyp : y ∉ FV p := by simpa [FV_ex, Ne.symm hay] using hy
          have hyq := ih hyp
          intro hmem
          exact (substVar_not_mem_FV_of_ne (a := a) (b := w)
            (Ne.symm hwy) hyq) hmem.1
      · rename_i hnot
        have hay : a ≠ y := fun h => hnot (Or.inl h)
        have hyp : y ∉ FV p := by simpa [FV_ex, Ne.symm hay] using hy
        simpa [FV_ex, Ne.symm hay] using ih hyp

private theorem avoidBinder_eq_self_of_avoids {t : Nat} {p : Pattern S Nat}
    (h : AvoidsBinder t p) : avoidBinder t p = p := by
  induction p with
  | var a => rfl
  | bot => rfl
  | app sigma args ih =>
      simp only [avoidBinder]
      congr
      funext i
      exact ih i (h i)
  | imp p q ihp ihq => simp [avoidBinder, ihp h.1, ihq h.2]
  | ex a p ih => simp [avoidBinder, h.1, ih h.2]

private theorem substVar_comp_of_fresh {x y z : Nat} {p : Pattern S Nat}
    (hy : y ∉ FV p) (hay : AvoidsBinder y p) (haz : AvoidsBinder z p) :
    substVar y z (substVar x y p) = substVar x z p := by
  induction p with
  | var a =>
      simp only [FV_var, Set.mem_singleton_iff] at hy
      by_cases hax : a = x <;> simp [substVar, hax, Ne.symm hy]
  | bot => rfl
  | app sigma args ih =>
      simp only [FV_app, Set.mem_iUnion, not_exists] at hy
      simp only [substVar]
      congr
      funext i
      exact ih i (hy i) (hay i) (haz i)
  | imp p q ihp ihq =>
      simp only [FV_imp, Set.mem_union, not_or] at hy
      simp [substVar, ihp hy.1 hay.1 haz.1, ihq hy.2 hay.2 haz.2]
  | ex a p ih =>
      have hay' : a ≠ y := hay.1
      have haz' : a ≠ z := haz.1
      have hyp : y ∉ FV p := by simpa [FV_ex, Ne.symm hay'] using hy
      by_cases hax : a = x
      · subst a
        have hself := substVar_eq_self_of_not_mem_FV (a := y) (b := z) hyp
        simp [substVar, hself]
      · simp [substVar, hax, hay', ih hyp hay.2 haz.2]

private def witnessBody (sigma : S.Sym)
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (p : Pattern S Nat)
    (x : Nat) (w : Fin (S.arity sigma) -> Nat) : Pattern S Nat :=
  .app sigma (fun i => Pattern.and (Phi i)
    (.imp (.ex x p) (captureAvoidingSubst x (w i) p)))

private theorem substVar_witnessBody_update {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (p : Pattern S Nat)
    (x : Nat) (w : Fin (S.arity sigma) -> Nat)
    (i : Fin (S.arity sigma)) (z : Nat)
    (hwP : ∀ j, w j ∉ p.allVars)
    (hwPhi : ∀ j k, w j ∉ (Phi k).allVars)
    (hwi : ∀ j, j ≠ i -> w i ≠ w j)
    (hz : z ∉ (witnessBody sigma Phi p x w).allVars) :
    substVar (w i) z (witnessBody sigma Phi p x w) =
      witnessBody sigma Phi p x (Function.update w i z) := by
  have hzarg : ∀ j, z ∉
      (Pattern.and (Phi j)
        (.imp (.ex x p) (captureAvoidingSubst x (w j) p))).allVars := by
    intro j hmem
    apply hz
    simp only [witnessBody, allVars, Finset.mem_biUnion,
      Finset.mem_univ, true_and]
    exact ⟨j, hmem⟩
  have hzPhi : ∀ j, z ∉ (Phi j).allVars := by
    intro j hmem
    exact hzarg j (by simp [allVars, hmem])
  have hzP : z ∉ p.allVars := by
    intro hmem
    exact hzarg i (by simp [allVars, hmem])
  have hzSub : z ∉ (substVar x (w i) p).allVars := by
    rw [← captureAvoidingSubst_eq_substVar_of_fresh (hwP i)]
    intro hmem
    exact hzarg i (by simp [allVars, hmem])
  simp only [witnessBody, substVar]
  congr
  funext j
  have hPhiRaw : substVar (w i) z (Phi j) = Phi j :=
    substVar_eq_self_of_not_mem_FV (fun h => hwPhi i j ((Phi j).FV_subset_allVars h))
  have hPRaw : substVar (w i) z p = p :=
    substVar_eq_self_of_not_mem_FV (fun h => hwP i (p.FV_subset_allVars h))
  have hcond : ¬ x = w i -> substVar (w i) z p = p := fun _ => hPRaw
  by_cases hji : j = i
  · subst j
    have hzCA : z ∉ (captureAvoidingSubst x (w i) p).allVars := by
      simpa [captureAvoidingSubst_eq_substVar_of_fresh (hwP i)] using hzSub
    have hcur : substVar (w i) z (captureAvoidingSubst x (w i) p) =
        captureAvoidingSubst x z p := by
      have hc := captureAvoidingSubst_comp_eq_of_fresh_result
        (x := x) (y := w i) (z := z) (p := p) (hwP i) hzP hzSub
      simpa [captureAvoidingSubst_eq_substVar_of_fresh hzCA] using hc
    simpa only [Function.update_self, imp.injEq, ite_eq_left_iff, ex.injEq,
      true_and, and_true] using And.intro hPhiRaw (And.intro hcond hcur)
  · have hwne : w i ≠ w j := hwi j hji
    have hother : substVar (w i) z (captureAvoidingSubst x (w j) p) =
        captureAvoidingSubst x (w j) p :=
      substVar_eq_self_of_not_mem_FV
        (captureAvoidingSubst_not_mem_FV_of_ne hwne
          (fun h => hwP i (p.FV_subset_allVars h)))
    have hupdate : Function.update w i z j = w j := by simp [hji]
    simpa only [hupdate, imp.injEq, ite_eq_left_iff, ex.injEq, true_and,
      and_true] using And.intro hPhiRaw (And.intro hcond hother)

private theorem substVar_exList {a b : Nat} (ys : List Nat)
    (q : Pattern S Nat) (ha : ∀ y ∈ ys, a ≠ y) :
    substVar a b (exList ys q) = exList ys (substVar a b q) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
      have hay : a ≠ y := ha y (by simp)
      simp only [exList, substVar, ite_eq_right (Ne.symm hay)]
      rw [ih (fun u hu => ha u (by simp [hu]))]

private theorem allVars_subset_exList (ys : List Nat) (q : Pattern S Nat) :
    q.allVars ⊆ (exList ys q).allVars := by
  induction ys with
  | nil => exact fun _ h => h
  | cons y ys ih =>
      intro a ha
      simp only [exList, allVars, Finset.mem_insert]
      exact Or.inr (ih ha)

private theorem mem_allVars_exList_of_mem {a : Nat} {ys : List Nat}
    {q : Pattern S Nat} (ha : a ∈ ys) : a ∈ (exList ys q).allVars := by
  induction ys with
  | nil => simp at ha
  | cons y ys ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [exList, allVars]
      · simp only [exList, allVars, Finset.mem_insert]
        exact Or.inr (ih ha)

private theorem IsMCS.exList_witness_elim_aux {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) (hW : FreshWitnessed Gamma) {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (p : Pattern S Nat)
    (x : Nat) (is : List (Fin (S.arity sigma)))
    (his : is.Nodup) (w : Fin (S.arity sigma) -> Nat)
    (hwP : ∀ j, w j ∉ p.allVars)
    (hwPhi : ∀ j k, w j ∉ (Phi k).allVars)
    (hwdist : ∀ i ∈ is, ∀ j, i ≠ j -> w i ≠ w j)
    (hmem : Pattern.exList (is.map w) (Pattern.witnessBody sigma Phi p x w) ∈ Gamma) :
    ∃ out : Fin (S.arity sigma) -> Nat,
      (∀ j, out j ∉ p.allVars) ∧
      (∀ j k, out j ∉ (Phi k).allVars) ∧
      Pattern.witnessBody sigma Phi p x out ∈ Gamma := by
  induction is generalizing w with
  | nil =>
      exact ⟨w, hwP, hwPhi, by simpa [Pattern.exList] using hmem⟩
  | cons i is ih =>
      have hi : i ∉ is := (List.nodup_cons.mp his).1
      have his' : is.Nodup := (List.nodup_cons.mp his).2
      have hhead : Pattern.ex (w i)
          (Pattern.exList (is.map w) (Pattern.witnessBody sigma Phi p x w)) ∈ Gamma := by
        simpa [Pattern.exList] using hmem
      obtain ⟨z, hzq, hsub⟩ := hM.freshWitness_elim hW hhead
      have hraw : substVar (w i) z
          (Pattern.exList (is.map w) (Pattern.witnessBody sigma Phi p x w)) ∈ Gamma := by
        simpa [Pattern.captureAvoidingSubst_eq_substVar_of_fresh hzq] using hsub
      have hdist : ∀ a ∈ is.map w, w i ≠ a := by
        intro a ha
        rcases List.mem_map.mp ha with ⟨j, hj, rfl⟩
        exact hwdist i (by simp) j (fun h => hi (h ▸ hj))
      have hzbody : z ∉ (Pattern.witnessBody sigma Phi p x w).allVars := by
        intro hzmem
        exact hzq (Pattern.allVars_subset_exList (is.map w)
          (Pattern.witnessBody sigma Phi p x w) hzmem)
      let w' := Function.update w i z
      have hbody : substVar (w i) z (Pattern.witnessBody sigma Phi p x w) =
          Pattern.witnessBody sigma Phi p x w' := by
        apply Pattern.substVar_witnessBody_update Phi p x w i z hwP hwPhi
        · intro j hji
          exact hwdist i (by simp) j hji.symm
        · exact hzbody
      have hzTail : ∀ a ∈ is, z ≠ w a := by
        intro a ha hEq
        apply hzq
        rw [hEq]
        exact Pattern.mem_allVars_exList_of_mem (List.mem_map.mpr ⟨a, ha, rfl⟩)
      have htailNames : is.map w' = is.map w := by
        apply List.map_congr_left
        intro j hj
        have hji : j ≠ i := fun h => hi (h ▸ hj)
        simp [w', hji]
      have hnext : Pattern.exList (is.map w')
          (Pattern.witnessBody sigma Phi p x w') ∈ Gamma := by
        rw [Pattern.substVar_exList (is.map w)
          (Pattern.witnessBody sigma Phi p x w) hdist] at hraw
        rw [hbody] at hraw
        simpa [htailNames] using hraw
      have hzarg : ∀ j, z ∉
          (Pattern.and (Phi j)
            (.imp (.ex x p) (Pattern.captureAvoidingSubst x (w j) p))).allVars := by
        intro j hzmem
        exact hzbody (by
          simp only [Pattern.witnessBody, Pattern.allVars,
            Finset.mem_biUnion, Finset.mem_univ, true_and]
          exact ⟨j, hzmem⟩)
      have hzP : z ∉ p.allVars := by
        intro hzmem
        exact hzarg i (by simp [Pattern.allVars, hzmem])
      have hzPhi : ∀ j, z ∉ (Phi j).allVars := by
        intro j hzmem
        exact hzarg j (by simp [Pattern.allVars, hzmem])
      have hwP' : ∀ j, w' j ∉ p.allVars := by
        intro j
        by_cases hji : j = i
        · subst j
          simpa [w'] using hzP
        · simpa [w', hji] using hwP j
      have hwPhi' : ∀ j k, w' j ∉ (Phi k).allVars := by
        intro j k
        by_cases hji : j = i
        · subst j
          simpa [w'] using hzPhi k
        · simpa [w', hji] using hwPhi j k
      have hwdist' : ∀ a ∈ is, ∀ b, a ≠ b -> w' a ≠ w' b := by
        intro a ha b hab
        have hai : a ≠ i := fun h => hi (h ▸ ha)
        by_cases hbi : b = i
        · subst b
          simpa [w', hai] using (hzTail a ha).symm
        · simpa [w', hai, hbi] using hwdist a (by simp [ha]) b hab
      exact ih his' w' hwP' hwPhi' hwdist' hnext

/-- Source substitution composition modulo alpha equivalence.  The intermediate
name is fresh only from free variables; the final name is arbitrary. -/
theorem captureAvoidingSubst_comp_alphaEq {x y z : Nat}
    {p : Pattern S Nat} (hy : y ∉ FV p) :
    AlphaEq
      (captureAvoidingSubst y z (captureAvoidingSubst x y p))
      (captureAvoidingSubst x z p) := by
  let q := avoidTwo y z p
  have halpha : AlphaEq p q := avoidTwo_alphaEq y z p
  have hqy : y ∉ FV q := avoidTwo_not_mem_FV hy
  have havoids := avoidTwo_avoids y z p
  have hleft : AlphaEq
      (captureAvoidingSubst y z (captureAvoidingSubst x y p))
      (captureAvoidingSubst y z (captureAvoidingSubst x y q)) :=
    (halpha.captureAvoidingSubst x y).captureAvoidingSubst y z
  have hright : AlphaEq (captureAvoidingSubst x z p)
      (captureAvoidingSubst x z q) := halpha.captureAvoidingSubst x z
  have hraw : substVar y z (substVar x y q) = substVar x z q :=
    substVar_comp_of_fresh hqy havoids.1 havoids.2
  have hmid : AlphaEq
      (captureAvoidingSubst y z (captureAvoidingSubst x y q))
      (captureAvoidingSubst x z q) := by
    have hby : avoidBinder y q = q := avoidBinder_eq_self_of_avoids havoids.1
    have hbz : avoidBinder z q = q := avoidBinder_eq_self_of_avoids havoids.2
    have hbzs : avoidBinder z (substVar x y q) = substVar x y q :=
      avoidBinder_eq_self_of_avoids havoids.2.substVar
    change AlphaEq
      (substVar y z (avoidBinder z (substVar x y (avoidBinder y q))))
      (substVar x z (avoidBinder z q))
    rw [hby, hbz, hbzs, hraw]
    exact AlphaEq.refl _
  exact hleft.trans (hmid.trans hright.symm)

end Pattern

/-- Eliminate the nested witnesses produced by Lemma 80 and normalize every
sequential raw substitution back to one source-style substitution. -/
theorem IsMCS.exList_witness_elim {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) (hW : FreshWitnessed Gamma) {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (p : Pattern S Nat)
    (x : Nat) (y : Fin (S.arity sigma) -> Nat)
    (hyinj : Function.Injective y)
    (hyfreshP : forall i, y i ∉ p.allVars)
    (hyfreshPhi : forall i j, y i ∉ (Phi j).allVars)
    (hnested : Pattern.exList (List.ofFn y)
      (.app sigma (fun i => Pattern.and (Phi i)
        (.imp (.ex x p) (Pattern.captureAvoidingSubst x (y i) p)))) ∈ Gamma) :
    ∃ z : Fin (S.arity sigma) -> Nat,
      (forall i, z i ∉ p.allVars) ∧
      (forall i j, z i ∉ (Phi j).allVars) ∧
      Pattern.app sigma (fun i => Pattern.and (Phi i)
        (.imp (.ex x p) (Pattern.captureAvoidingSubst x (z i) p))) ∈ Gamma := by
  let ids := List.ofFn (fun i : Fin (S.arity sigma) => i)
  have hids : ids.Nodup := by
    dsimp [ids]
    rw [List.nodup_ofFn]
    exact Function.injective_id
  have hnested' : Pattern.exList (ids.map y)
      (Pattern.witnessBody sigma Phi p x y) ∈ Gamma := by
    simpa [ids, Pattern.witnessBody, List.map_ofFn, Function.comp_def] using hnested
  have hdist : ∀ i ∈ ids, ∀ j, i ≠ j -> y i ≠ y j := by
    intro i _ j hij
    exact hyinj.ne hij
  simpa [Pattern.witnessBody] using
    (Pattern.IsMCS.exList_witness_elim_aux hM hW Phi p x ids hids y
      hyfreshP hyfreshPhi hdist hnested')

/-- Stage-recursion interface: apply Lemma 80 and immediately eliminate its
nested witnesses inside a witnessed MCS. -/
theorem IsMCS.witnessPush_elim {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) (hW : FreshWitnessed Gamma) {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (p : Pattern S Nat)
    (x : Nat) (y : Fin (S.arity sigma) -> Nat)
    (hyinj : Function.Injective y)
    (hyfreshP : forall i, y i ∉ p.allVars)
    (hyfreshPhi : forall i j, y i ∉ (Phi j).allVars)
    (happ : Pattern.app sigma Phi ∈ Gamma) :
    ∃ z : Fin (S.arity sigma) -> Nat,
      (forall i, z i ∉ p.allVars) ∧
      (forall i j, z i ∉ (Phi j).allVars) ∧
      Pattern.app sigma (fun i => Pattern.and (Phi i)
        (.imp (.ex x p) (Pattern.captureAvoidingSubst x (z i) p))) ∈ Gamma := by
  have hpush : Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma Phi)
        (Pattern.exList (List.ofFn y)
          (.app sigma (fun i => Pattern.and (Phi i)
            (.imp (.ex x p) (Pattern.captureAvoidingSubst x (y i) p)))))) := by
    exact Provable.witnessPush Phi p x y hyinj
      (fun i h => hyfreshP i (p.FV_subset_allVars h))
      (fun i j h => hyfreshPhi i j ((Phi j).FV_subset_allVars h))
  have hnested : Pattern.exList (List.ofFn y)
      (.app sigma (fun i => Pattern.and (Phi i)
        (.imp (.ex x p) (Pattern.captureAvoidingSubst x (y i) p)))) ∈ Gamma :=
    hM.mem_of_provable_imp happ hpush
  exact hM.exList_witness_elim hW Phi p x y hyinj hyfreshP hyfreshPhi hnested

end MatchingLogic
