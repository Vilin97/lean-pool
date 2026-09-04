/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.SkolemColimit
/-!
# Staged set-closure (generic core for the Skolem-closed family `Γ*`)

The bespoke EM truth lemma inducts over a countable formula family `Γ*` that is closed under
subformulas, countable-connective components, existential Skolem-witness instances, and the
template renamings. This file provides the **language-agnostic** staged-closure machinery — closing
a seed set `Γ₀` under a pointwise expansion `stepOne : α → Set α` via explicit stages (no
impredicative least-closure) — together with countability and the consumer-facing closure lemma.

The concrete formula `stepOne` (subformulas / components / Skolem witnesses / renamings) inside
`skolemColim L` is layered on top in a later chunk; `Γ*` will be `setClosure` of that step applied
to the lifted EM starting family.
-/

namespace FirstOrder.Language

variable {α : Type*}

/-- Stages of closing `Γ₀` under the pointwise expansion `stepOne`: stage `0` is the seed, each
successor adds `stepOne x` for every `x` already present. Increasing by construction. -/
def iterClosure (stepOne : α → Set α) (Γ₀ : Set α) : ℕ → Set α
  | 0 => Γ₀
  | k + 1 => iterClosure stepOne Γ₀ k ∪ ⋃ x ∈ iterClosure stepOne Γ₀ k, stepOne x

/-- The **staged closure** of `Γ₀` under `stepOne`: the union over all finite stages. -/
def setClosure (stepOne : α → Set α) (Γ₀ : Set α) : Set α :=
  ⋃ k, iterClosure stepOne Γ₀ k

/-- The seed is contained in the closure (it is stage `0`). -/
theorem subset_setClosure (stepOne : α → Set α) (Γ₀ : Set α) : Γ₀ ⊆ setClosure stepOne Γ₀ :=
  Set.subset_iUnion (iterClosure stepOne Γ₀) 0

/-- **Closure property** (consumer-facing): the expansion of any member stays in the closure. If
`x ∈ Γ*` then `stepOne x ⊆ Γ*`. -/
theorem stepOne_subset_setClosure (stepOne : α → Set α) (Γ₀ : Set α) {x : α}
    (hx : x ∈ setClosure stepOne Γ₀) : stepOne x ⊆ setClosure stepOne Γ₀ := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  intro y hy
  exact Set.mem_iUnion.mpr ⟨k + 1, Or.inr (Set.mem_biUnion hk hy)⟩

/-- Each stage is countable, given a countable seed and a pointwise-countable step. -/
theorem iterClosure_countable (stepOne : α → Set α) {Γ₀ : Set α} (hΓ₀ : Γ₀.Countable)
    (hstep : ∀ x, (stepOne x).Countable) : ∀ k, (iterClosure stepOne Γ₀ k).Countable := by
  intro k
  induction k with
  | zero => exact hΓ₀
  | succ k ih => exact ih.union (ih.biUnion fun x _ => hstep x)

/-- The closure is countable, given a countable seed and a pointwise-countable step. -/
theorem setClosure_countable (stepOne : α → Set α) {Γ₀ : Set α} (hΓ₀ : Γ₀.Countable)
    (hstep : ∀ x, (stepOne x).Countable) : (setClosure stepOne Γ₀).Countable :=
  Set.countable_iUnion (iterClosure_countable stepOne hΓ₀ hstep)

/-! ### Subformula / connective-component step (any language) -/

/-- Immediate subformulas and countable-connective components of a formula, over **any** language:
`imp` gives both parts, `all` gives the body (one higher arity), `iSup`/`iInf` give all
countably-many components, and the atomic forms give none. -/
def bfSubformulas {Λ : Language.{0, 0}} :
    (Σ n, Λ.BoundedFormulaω Empty n) → Set (Σ n, Λ.BoundedFormulaω Empty n)
  | ⟨_, .imp φ ψ⟩ => {⟨_, φ⟩, ⟨_, ψ⟩}
  | ⟨_, .all φ⟩ => {⟨_, φ⟩}
  | ⟨_, .iSup φs⟩ => Set.range fun k => ⟨_, φs k⟩
  | ⟨_, .iInf φs⟩ => Set.range fun k => ⟨_, φs k⟩
  | _ => ∅

/-- `bfSubformulas` is pointwise countable. -/
theorem bfSubformulas_countable {Λ : Language.{0, 0}} (χ : Σ n, Λ.BoundedFormulaω Empty n) :
    (bfSubformulas χ).Countable := by
  obtain ⟨n, φ⟩ := χ
  cases φ with
  | imp φ ψ => exact (Set.countable_singleton _).insert _
  | all φ => exact Set.countable_singleton _
  | iSup φs => exact Set.countable_range _
  | iInf φs => exact Set.countable_range _
  | falsum => exact Set.countable_empty
  | equal _ _ => exact Set.countable_empty
  | rel _ _ => exact Set.countable_empty

/-! ### Staged formulas and the colimit projection -/

variable (L : Language.{0, 0})

/-- A colimit-language formula packaged with its arity. -/
abbrev ColimFormula := Σ n, (skolemColim L).BoundedFormulaω Empty n

/-- A formula tagged with the finite language **stage** at which it lives. The closure works at
this staged level — so the existential-witness Skolem term is directly available at the next stage
— and projects to a colimit formula only via `toColimFormula`. This avoids ever inverting the
colimit quotient. -/
abbrev SkFormula := Σ k : ℕ, Σ n : ℕ, (skolemStage L k).BoundedFormulaω Empty n

/-- Project a staged formula to a colimit-language formula, transporting along the stage inclusion
`skolemStageInclusion L k`. `Γ*` in the colimit language is the image of the staged closure under
this map. -/
def toColimFormula : SkFormula L → ColimFormula L
  | ⟨k, n, φ⟩ => ⟨n, φ.mapLanguage (skolemStageInclusion L k)⟩

/-- The subformula/component step at the **staged** level: take `bfSubformulas` of the stage-`k`
formula, keeping the stage `k` fixed. -/
def skSubStep : SkFormula L → Set (SkFormula L)
  | ⟨k, χ⟩ => (fun p => (⟨k, p⟩ : SkFormula L)) '' bfSubformulas χ

/-- The staged subformula step is pointwise countable. -/
theorem skSubStep_countable (χ : SkFormula L) : (skSubStep L χ).Countable := by
  obtain ⟨k, χ⟩ := χ
  exact (bfSubformulas_countable χ).image _

/-! ### Existential Skolem-witness step (stage `k` → `k+1`) -/

/-- The **Skolem-witness body** of `∃x ψ` (with `ψ` the `(n+1)`-ary matrix at stage `k`): substitute
the stage-`(k+1)` Skolem term `skolemTerm ψ` (of the remaining `n` variables) for the witnessed
variable. Built with the template substitution pattern `openBounds → subst → relabel`, placing the
Skolem term in the last slot. Lives at stage `k+1` and arity `n`. -/
def skolemWitnessFormula {k n : ℕ} (ψ : (skolemStage L k).BoundedFormulaω Empty (n + 1)) :
    (skolemStage L (k + 1)).BoundedFormulaω Empty n :=
  (((ψ.openBounds.mapLanguage (skolemStageHom L k)).subst
    (Fin.snoc (fun i => Term.var i) (skolemTerm ψ (fun i => Term.var i)))).relabel Sum.inr)

/-- The **Skolem-witness step**: Skolemize the (primitive) universal quantifier. For `∀x φ` at
stage `k`, add the witness body of its negation `∃x ¬φ`, namely `(¬φ)[skolemTerm (¬φ)]`, at stage
`k+1`. Since `∃xψ = ¬∀x¬ψ`, this covers existentials too. Other forms add nothing. -/
def skWitnessStep : SkFormula L → Set (SkFormula L)
  | ⟨k, n, .all φ⟩ => {⟨k + 1, n, skolemWitnessFormula L φ.not⟩}
  | _ => ∅

/-- The Skolem-witness step is pointwise countable (a singleton on `∀`, empty otherwise). -/
theorem skWitnessStep_countable (χ : SkFormula L) : (skWitnessStep L χ).Countable := by
  obtain ⟨k, n, φ⟩ := χ
  cases φ <;> first | exact Set.countable_singleton _ | exact Set.countable_empty

/-! ### The Skolem-closed staged family `Γ*` -/

/-- The full staged closure step: subformulas/components together with Skolem witnesses. (Template
renamings are added where the truth lemma needs them, in a later chunk.) -/
def skStep (χ : SkFormula L) : Set (SkFormula L) := skSubStep L χ ∪ skWitnessStep L χ

theorem skStep_countable (χ : SkFormula L) : (skStep L χ).Countable :=
  (skSubStep_countable L χ).union (skWitnessStep_countable L χ)

/-- The **Skolem-closed staged family** generated by a seed set of staged formulas. -/
def Γstar (Γ₀ : Set (SkFormula L)) : Set (SkFormula L) := setClosure (skStep L) Γ₀

/-- `Γ*` is countable when the seed is. -/
theorem Γstar_countable {Γ₀ : Set (SkFormula L)} (hΓ₀ : Γ₀.Countable) : (Γstar L Γ₀).Countable :=
  setClosure_countable (skStep L) hΓ₀ (skStep_countable L)

/-- The seed is contained in `Γ*`. -/
theorem subset_Γstar (Γ₀ : Set (SkFormula L)) : Γ₀ ⊆ Γstar L Γ₀ := subset_setClosure _ _

/-- **Closure property** of `Γ*`: the full step of any member stays in `Γ*`. -/
theorem skStep_subset_Γstar {Γ₀ : Set (SkFormula L)} {χ : SkFormula L} (hχ : χ ∈ Γstar L Γ₀) :
    skStep L χ ⊆ Γstar L Γ₀ := stepOne_subset_setClosure _ _ hχ

/-- Subformulas/components of a `Γ*` member stay in `Γ*`. -/
theorem skSubStep_subset_Γstar {Γ₀ : Set (SkFormula L)} {χ : SkFormula L} (hχ : χ ∈ Γstar L Γ₀) :
    skSubStep L χ ⊆ Γstar L Γ₀ :=
  (Set.subset_union_left).trans (skStep_subset_Γstar L hχ)

/-- The Skolem witness of a `Γ*` member stays in `Γ*`. -/
theorem skWitnessStep_subset_Γstar {Γ₀ : Set (SkFormula L)} {χ : SkFormula L}
    (hχ : χ ∈ Γstar L Γ₀) : skWitnessStep L χ ⊆ Γstar L Γ₀ :=
  (Set.subset_union_right).trans (skStep_subset_Γstar L hχ)

/-! ### Colimit image and enumeration -/

/-- The colimit-language image of `Γ*` is countable. -/
theorem toColimFormula_image_Γstar_countable {Γ₀ : Set (SkFormula L)} (hΓ₀ : Γ₀.Countable) :
    (toColimFormula L '' Γstar L Γ₀).Countable :=
  (Γstar_countable L hΓ₀).image _

/-- An **enumeration** of `Γ*`'s colimit image as a sequence `ℕ → ColimFormula L`, suitable as the
formula family fed to `morleyHanfExtractionTail_holds` (whose extraction yields tail-indiscernibility
on `Set.range`). Exists since the image is countable and nonempty. -/
theorem exists_ΓEnum {Γ₀ : Set (SkFormula L)} (hΓ₀ : Γ₀.Countable)
    (hne : (toColimFormula L '' Γstar L Γ₀).Nonempty) :
    ∃ ΓEnum : ℕ → ColimFormula L, toColimFormula L '' Γstar L Γ₀ = Set.range ΓEnum :=
  (toColimFormula_image_Γstar_countable L hΓ₀).exists_eq_range hne

end FirstOrder.Language
