/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Soundness of Figure 2 — (S) of arXiv:2608.13306v1, Section 2.

The paper uses (S) as a black box, citing it to its reference [3]. It is one of
the two hypotheses that entry point (ii) of the mechanization challenge is
allowed to assume. But unlike (L), which rests on a canonical-model
construction, soundness is a rule-by-rule induction — so discharging it here
removes one of the two black boxes from Corollary 15.

Statement pinned before any proof was attempted.
-/
import LeanPool.MatchingLogic.ProofSystem
import LeanPool.MatchingLogic.Sanity

/-!
# MatchingLogic.Soundness
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

attribute [local instance] Classical.propDecidable

/-- Raw variable substitution is inert when its source variable is not free. -/
theorem Pattern.substVar_eq_self_of_not_mem_FV {x y : Var} {φ : Pattern S Var}
    (hx : x ∉ FV φ) : substVar x y φ = φ := by
  induction φ with
  | var z =>
      simp only [FV_var, Set.mem_singleton_iff] at hx
      have hzx : z ≠ x := fun h => hx h.symm
      change (if z = x then Pattern.var y else Pattern.var z) = Pattern.var z
      rw [ite_eq_right hzx]
  | bot => rfl
  | app σ f ih =>
      simp only [FV_app, Set.mem_iUnion, not_exists] at hx
      simp only [substVar]
      congr 2
      funext i
      exact ih i (hx i)
  | imp φ ψ ihφ ihψ =>
      simp only [FV_imp, Set.mem_union, not_or] at hx
      simp [substVar, ihφ hx.1, ihψ hx.2]
  | ex z φ ih =>
      by_cases hzx : z = x
      · simp [substVar, hzx]
      · simp only [FV_ex, Set.mem_sdiff, Set.mem_singleton_iff, not_and_or,
          Classical.not_not] at hx
        have hxφ : x ∉ FV φ := by
          intro hmem
          exact hx.resolve_right (fun h => hzx h.symm) hmem
        simp [substVar, hzx, ih hxφ]

/-- Semantic substitution for the capture-free variable-for-variable
substitution used by rule (3). -/
theorem Model.denote_substVar_of_captureFree (M : Model S) (ρ : Var → M.carrier)
    {x y : Var} {φ : Pattern S Var} (hcf : CaptureFree x y φ) :
    M.denote ρ (substVar x y φ) =
      M.denote (Function.update ρ x (ρ y)) φ := by
  induction φ generalizing ρ with
  | var z =>
      by_cases hzx : z = x
      · subst z
        simp [substVar]
      · simp [substVar, hzx]
  | bot => simp [substVar]
  | app σ f ih =>
      simp only [substVar, denote_app]
      congr 2
      funext i
      exact ih i ρ (hcf i)
  | imp φ ψ ihφ ihψ =>
      exact congrArg₂ (fun A B : Set M.carrier => Aᶜ ∪ B)
        (ihφ ρ hcf.1) (ihψ ρ hcf.2)
  | ex z φ ih =>
      rcases hcf with hzx | hxfree | ⟨hzy, hrec⟩
      · subst z
        simp [substVar]
      · by_cases hzx : z = x
        · subst z
          simp [substVar]
        · rw [substVar]
          simp only [ite_eq_right hzx, denote_ex]
          congr 1
          funext a
          rw [Pattern.substVar_eq_self_of_not_mem_FV hxfree]
          apply denote_congr M φ
          intro q hq
          have hqx : q ≠ x := fun h => hxfree (h ▸ hq)
          by_cases hqz : q = z
          · subst q
            simp
          · simp [hqz, hqx]
      · by_cases hzx : z = x
        · subst z
          simp [substVar]
        · rw [substVar]
          simp only [ite_eq_right hzx, denote_ex]
          congr 1
          funext a
          rw [ih (Function.update ρ z a) hrec]
          congr 1
          funext q
          by_cases hqz : q = z
          · subst q
            simp [Function.update_apply, hzx]
          · by_cases hqx : q = x
            · subst q
              simp [Ne.symm hzy, hqz]
            · simp [Function.update_apply, hqz, hqx]

private theorem pform_mem_denote_iff (M : Model S) (ρ : Var → M.carrier)
    (θ : Nat → Pattern S Var) (u : M.carrier) (p : PForm) :
    u ∈ M.denote ρ (p.subst θ) ↔
      p.eval (fun n => decide (u ∈ M.denote ρ (θ n))) = true := by
  induction p with
  | atom n => simp [PForm.subst, PForm.eval]
  | bot => simp [PForm.subst, PForm.eval]
  | imp p q ihp ihq =>
      simp [PForm.subst, PForm.eval, ihp, ihq]

private theorem pform_taut_total (M : Model S) (ρ : Var → M.carrier)
    (θ : Nat → Pattern S Var) {p : PForm} (hp : p.Taut) :
    M.denote ρ (p.subst θ) = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro u
  apply (pform_mem_denote_iff M ρ θ u p).mpr
  exact hp (fun n => decide (u ∈ M.denote ρ (θ n)))

private theorem Model.app_update_union (M : Model S) (σ : S.Sym)
    (A : Fin (S.arity σ) → Set M.carrier) (i : Fin (S.arity σ))
    (B C : Set M.carrier) :
    M.app σ (Function.update A i (B ∪ C)) =
      M.app σ (Function.update A i B) ∪
        M.app σ (Function.update A i C) := by
  ext u
  constructor
  · rintro ⟨a, ha, hu⟩
    have hai : a i ∈ B ∪ C := by simpa using ha i
    rcases hai with hi | hi
    · left
      exact ⟨a, fun j => by
        by_cases hji : j = i
        · subst j
          simpa using hi
        · simpa [Function.update_apply, hji] using ha j, hu⟩
    · right
      exact ⟨a, fun j => by
        by_cases hji : j = i
        · subst j
          simpa using hi
        · simpa [Function.update_apply, hji] using ha j, hu⟩
  · rintro (⟨a, ha, hu⟩ | ⟨a, ha, hu⟩)
    · exact ⟨a, fun j => by
        by_cases hji : j = i
        · subst j
          simpa using (show a i ∈ B ∪ C from Or.inl (by simpa using ha i))
        · simpa [Function.update_apply, hji] using ha j, hu⟩
    · exact ⟨a, fun j => by
        by_cases hji : j = i
        · subst j
          simpa using (show a i ∈ B ∪ C from Or.inr (by simpa using ha i))
        · simpa [Function.update_apply, hji] using ha j, hu⟩

private theorem Model.app_mono_at (M : Model S) (σ : S.Sym)
    (A : Fin (S.arity σ) → Set M.carrier) (i : Fin (S.arity σ))
    {B C : Set M.carrier} (hBC : B ⊆ C) :
    M.app σ (Function.update A i B) ⊆
      M.app σ (Function.update A i C) := by
  rintro u ⟨a, ha, hu⟩
  exact ⟨a, fun j => by
    by_cases hji : j = i
    · subst j
      simpa using hBC (by simpa using ha i)
    · simpa [Function.update_apply, hji] using ha j, hu⟩

private theorem denote_app_update (M : Model S) (ρ : Var → M.carrier)
    (σ : S.Sym) (args : Fin (S.arity σ) → Pattern S Var)
    (i : Fin (S.arity σ)) (φ : Pattern S Var) :
    M.denote ρ (.app σ (Function.update args i φ)) =
      M.app σ (Function.update (fun j => M.denote ρ (args j)) i
        (M.denote ρ φ)) := by
  simp only [denote_app]
  congr 2
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

private theorem denote_or (M : Model S) (ρ : Var → M.carrier)
    (φ ψ : Pattern S Var) :
    M.denote ρ (Pattern.or φ ψ) = M.denote ρ φ ∪ M.denote ρ ψ := by
  simp [Pattern.or]

private theorem denote_and (M : Model S) (ρ : Var → M.carrier)
    (φ ψ : Pattern S Var) :
    M.denote ρ (Pattern.and φ ψ) = M.denote ρ φ ∩ M.denote ρ ψ := by
  simp [Pattern.and]

private theorem imp_total_of_subset (M : Model S) (ρ : Var → M.carrier)
    {φ ψ : Pattern S Var} (h : M.denote ρ φ ⊆ M.denote ρ ψ) :
    M.denote ρ (.imp φ ψ) = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro u
  by_cases hu : u ∈ M.denote ρ φ
  · exact Set.mem_union_right _ (h hu)
  · exact Set.mem_union_left _ hu

private theorem subset_of_imp_total (M : Model S) (ρ : Var → M.carrier)
    {φ ψ : Pattern S Var} (h : M.denote ρ (.imp φ ψ) = Set.univ) :
    M.denote ρ φ ⊆ M.denote ρ ψ := by
  intro u hu
  have hut : u ∈ M.denote ρ (.imp φ ψ) := by
    rw [h]
    exact Set.mem_univ u
  rcases hut with hnot | hψ
  · exact (hnot hu).elim
  · exact hψ

private theorem denote_appCtx_empty (M : Model S) (ρ : Var → M.carrier)
    (C : AppCtx S Var) {φ : Pattern S Var} (hφ : M.denote ρ φ = ∅) :
    M.denote ρ (C.plug φ) = ∅ := by
  induction C with
  | hole => exact hφ
  | node σ i args C ih =>
      simp only [AppCtx.plug, denote_app]
      apply Model.app_eq_empty M σ _ i
      simpa using ih

/-- **(S) is provable, not merely assumable.**  The paper cites soundness to its
reference [3]; every rule of Figure 2 is sound for global consequence, so it can
be discharged here.  Doing so removes one of the two black boxes from
Corollary 15. -/
theorem soundness : Soundness S Var := by
  intro Γ φ hprov
  induction hprov with
  | hyp hφ =>
      intro M hM
      exact hM _ hφ
  | taut hp =>
      intro M _ ρ
      exact pform_taut_total M ρ _ hp
  | mp hφ hφψ ihφ ihφψ =>
      intro M hM ρ
      exact Set.eq_univ_iff_forall.mpr fun u =>
        subset_of_imp_total M ρ (ihφψ M hM ρ)
          (by rw [ihφ M hM ρ]; exact Set.mem_univ u)
  | exQuant hcf =>
      intro M _ ρ
      apply imp_total_of_subset M ρ
      intro u hu
      rw [M.denote_substVar_of_captureFree ρ hcf] at hu
      exact Set.mem_iUnion.mpr ⟨ρ _, hu⟩
  | exGen hφψ hxfree ih =>
      rename_i x φ₁ φ₂
      intro M hM ρ
      apply imp_total_of_subset M ρ
      intro u hu
      obtain ⟨a, hua⟩ := Set.mem_iUnion.mp hu
      have huψ := subset_of_imp_total M (Function.update ρ x a)
        (ih M hM (Function.update ρ x a)) hua
      rw [denote_congr M φ₂ (Function.update ρ x a) ρ (by
        intro q hq
        have hqx : q ≠ x := fun h => hxfree (by simpa [h] using hq)
        simp [hqx])] at huψ
      exact huψ
  | propBot =>
      rename_i σ i args
      intro M _ ρ
      apply imp_total_of_subset M ρ
      rw [denote_app_update]
      rw [Model.app_eq_empty M σ _ i (by simp)]
      exact Set.empty_subset _
  | propOr =>
      intro M _ ρ
      apply imp_total_of_subset M ρ
      simp only [denote_app_update, denote_or]
      rw [Model.app_update_union]
  | propEx hfree =>
      rename_i σ i args x φ₀
      intro M _ ρ
      apply imp_total_of_subset M ρ
      simp only [denote_app_update]
      rintro u ⟨a, ha, hu⟩
      have hai : a i ∈ ⋃ b : M.carrier,
          M.denote (Function.update ρ x b) φ₀ := by simpa using ha i
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hai
      apply Set.mem_iUnion.mpr
      refine ⟨b, a, ?_, hu⟩
      intro j
      by_cases hji : j = i
      · subst j
        simpa using hb
      · have hden : M.denote (Function.update ρ x b) (args j) =
            M.denote ρ (args j) := by
          apply denote_congr M (args j)
          intro q hq
          have hqx : q ≠ x := fun h => hfree j hji (by simpa [h] using hq)
          simp [hqx]
        simpa [Function.update_apply, hji, hden] using ha j
  | framing hφψ ih =>
      intro M hM ρ
      apply imp_total_of_subset M ρ
      simp only [denote_app_update]
      apply Model.app_mono_at
      exact subset_of_imp_total M ρ (ih M hM ρ)
  | existence =>
      intro M _ ρ
      apply Set.eq_univ_iff_forall.mpr
      intro u
      exact Set.mem_iUnion.mpr ⟨u, by simp⟩
  | singleton C₁ C₂ =>
      rename_i x φ₀
      intro M _ ρ
      apply imp_total_of_subset M ρ
      by_cases hxφ : ρ x ∈ M.denote ρ φ₀
      · have hnegative :
            M.denote ρ (Pattern.and (.var x) (Pattern.nt φ₀)) = ∅ := by
          rw [denote_and, denote_var, denote_nt]
          ext u
          simp [hxφ]
        have hctx := denote_appCtx_empty M ρ C₂ hnegative
        rw [denote_nt, hctx]
        simp
      · have hpositive : M.denote ρ (Pattern.and (.var x) φ₀) = ∅ := by
          rw [denote_and, denote_var]
          ext u
          simp [hxφ]
        rw [denote_appCtx_empty M ρ C₁ hpositive]
        exact Set.empty_subset _

end MatchingLogic
