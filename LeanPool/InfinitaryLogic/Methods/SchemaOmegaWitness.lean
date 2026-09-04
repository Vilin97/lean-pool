/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LocalEMTemplateRealization
/-!
# Layer 7a: the schema-template Ω-witness bridge

The first, abstract chunk of the schema-level completion pivot (Layer 7). It connects a
**template-level** witness property — `TailTemplateOmegaWitnessed`, the `⋁`/`⋀` witnessing of
`tailTemplateOfSeq a` on the exact de-substituted formulas the source-side normal form uses —
to `LocalEMContext.OmegaCompleteForColim`, the hard input of the local-EM realization
`tailTemplateRealizable_of_localEMContext`.

The route deliberately goes **through the existing `LocalEMOmegaHomogeneous` normal form**,
not directly to `OmegaCompleteForColim`: `omegaCompleteForColim_of_omegaHomogeneous` already
converts `LocalEMOmegaHomogeneous` into `OmegaCompleteForColim`, so all this file must supply
is `TailTemplateOmegaWitnessed → LocalEMOmegaHomogeneous`, shuttled across the tail-template
truth collapse (`IsLomega1omegaIndiscernibleOnTail.tailTemplateOfSeq_truth_iff`): template
truth of a `canonDeForm` ⇔ its eventual truth on the consecutive deep tuples `k ↦ a (d+k)`.

No enumeration, Zorn, or term model appears here — this is the interface milestone that fixes
the shape the ω-stage completion (Layer 7b) must produce.
-/

namespace FirstOrder.Language

open Filter

variable {s₀ : LocalStage} {M : Type} [(localColim s₀).Structure M]

/-- **The schema-template Ω-witness property.** For the schema template `tailTemplateOfSeq a`,
over the canonical de-substituted formulas of colimit-family connectives: a disjunction's
template truth yields one component's template truth, and joint component template truth yields
the conjunction's. This is the countable, `J`-free witnessing the ω-stage Henkin completion
will establish; here it is the input to the normal-form bridge. -/
structure TailTemplateOmegaWitnessed (s₀ : LocalStage) {M : Type}
    [(localColim s₀).Structure M] (a : ℕ → M) : Prop where
  /-- A family disjunction's `canonDeForm` template-true ⟹ some component's is. -/
  iSup_witnessed : ∀ {m : ℕ} (φs : ℕ → (localColim s₀).BoundedFormulaω Empty m),
    (⟨m, BoundedFormulaω.iSup φs⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈
      ΓlocalColim s₀ →
    ∀ {p : ℕ} (g : Fin m → (localColim s₀).Term (Fin p)),
    (tailTemplateOfSeq (L := localColim s₀) a).truth
        (canonDeForm (localColim s₀) (BoundedFormulaω.iSup φs) g) →
    ∃ i, (tailTemplateOfSeq (L := localColim s₀) a).truth
        (canonDeForm (localColim s₀) (φs i) g)
  /-- All components' `canonDeForm` template-true ⟹ the family conjunction's is. -/
  iInf_witnessed : ∀ {m : ℕ} (φs : ℕ → (localColim s₀).BoundedFormulaω Empty m),
    (⟨m, BoundedFormulaω.iInf φs⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈
      ΓlocalColim s₀ →
    ∀ {p : ℕ} (g : Fin m → (localColim s₀).Term (Fin p)),
    (∀ i, (tailTemplateOfSeq (L := localColim s₀) a).truth
        (canonDeForm (localColim s₀) (φs i) g)) →
    (tailTemplateOfSeq (L := localColim s₀) a).truth
        (canonDeForm (localColim s₀) (BoundedFormulaω.iInf φs) g)

/-- A canonical deForm of a colimit-family member lands in `ΓEMlocal` (its `canonDeForms`
component). -/
theorem canonDeForm_mem_ΓEMlocal {m : ℕ} {φ : (localColim s₀).BoundedFormulaω Empty m}
    (hφ : (⟨m, φ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀)
    {p : ℕ} (g : Fin m → (localColim s₀).Term (Fin p)) :
    (⟨p, canonDeForm (localColim s₀) φ g⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈
      ΓEMlocal s₀ :=
  Set.mem_union_right _ (canonDeForm_mem_canonDeForms (localColim s₀) hφ g)

/-- **The tail-template truth collapse** (on the family `ΓEMlocal`): template truth of a member
formula is exactly its eventual truth on the consecutive deep tuples `k ↦ a (d+k)`. Forward is
"consecutive tuples are strictly-monotone deep tuples"; backward is the tail indiscernibility
(all sufficiently deep strict-mono tuples agree). -/
theorem tailTemplate_truth_iff_eventually {a : ℕ → M}
    (hTail : IsLomega1omegaIndiscernibleOnTail (L := localColim s₀) a (ΓEMlocal s₀))
    {p : ℕ} {ψ : (localColim s₀).BoundedFormulaω Empty p}
    (hψ : (⟨p, ψ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀) :
    (tailTemplateOfSeq (L := localColim s₀) a).truth ψ ↔
      ∀ᶠ d in atTop, ψ.Realize (Empty.elim : Empty → M) (fun k : Fin p => a (d + (k : ℕ))) := by
  obtain ⟨N, hN⟩ := hTail.tailTemplateOfSeq_truth_iff hψ
  have hsm : ∀ d : ℕ, StrictMono (fun k : Fin p => d + (k : ℕ)) :=
    fun d _ _ hij => Nat.add_lt_add_left hij d
  constructor
  · intro htruth
    refine eventually_atTop.mpr ⟨N, fun d hd => ?_⟩
    exact (hN (fun k => d + (k : ℕ)) (hsm d)
      (fun k => le_trans hd (Nat.le_add_right d (k : ℕ)))).mp htruth
  · intro hev
    obtain ⟨N', hN'⟩ := eventually_atTop.mp hev
    exact (hN (fun k => max N N' + (k : ℕ)) (hsm _)
      (fun k => le_trans (le_max_left N N') (Nat.le_add_right _ (k : ℕ)))).mpr
      (hN' (max N N') (le_max_right N N'))

/-- **The normal-form bridge**: the schema-template Ω-witness property, plus tail
indiscernibility of `a` on `ΓEMlocal`, implies the source-side normal form
`LocalEMOmegaHomogeneous`. Each clause is shuttled across the truth collapse: eventual
consecutive truth of the disjunction's deForm ⇒ its template truth ⇒ (witnessed) a component's
template truth ⇒ its eventual consecutive truth. `canonDeForm` distributes over the connectives
definitionally, so `realize_iSup`/`realize_iInf` move between the connective and its
components. -/
theorem TailTemplateOmegaWitnessed.to_localEMOmegaHomogeneous {a : ℕ → M}
    (hTail : IsLomega1omegaIndiscernibleOnTail (L := localColim s₀) a (ΓEMlocal s₀))
    (h : TailTemplateOmegaWitnessed s₀ a) : LocalEMOmegaHomogeneous s₀ a := by
  refine ⟨?_, ?_⟩
  · intro m φs hmem p g hev
    have hev2 : ∀ᶠ d in atTop, (canonDeForm (localColim s₀) (BoundedFormulaω.iSup φs) g).Realize
        (Empty.elim : Empty → M) (fun k : Fin p => a (d + (k : ℕ))) := by
      refine hev.mono fun d hd => ?_
      rw [show canonDeForm (localColim s₀) (BoundedFormulaω.iSup φs) g
          = BoundedFormulaω.iSup (fun i => canonDeForm (localColim s₀) (φs i) g) from rfl,
        BoundedFormulaω.realize_iSup]
      exact hd
    obtain ⟨i, htruthi⟩ := h.iSup_witnessed φs hmem g
      ((tailTemplate_truth_iff_eventually hTail (canonDeForm_mem_ΓEMlocal hmem g)).mpr hev2)
    exact ⟨i, (tailTemplate_truth_iff_eventually hTail
      (canonDeForm_mem_ΓEMlocal (iSup_component_mem_ΓlocalColim s₀ hmem i) g)).mp htruthi⟩
  · intro m φs hmem p g hev
    have htruthi : ∀ i, (tailTemplateOfSeq (L := localColim s₀) a).truth
        (canonDeForm (localColim s₀) (φs i) g) := fun i =>
      (tailTemplate_truth_iff_eventually hTail
        (canonDeForm_mem_ΓEMlocal (iInf_component_mem_ΓlocalColim s₀ hmem i) g)).mpr (hev i)
    have hevInf := (tailTemplate_truth_iff_eventually hTail (canonDeForm_mem_ΓEMlocal hmem g)).mp
      (h.iInf_witnessed φs hmem g htruthi)
    refine hevInf.mono fun d hd => ?_
    rw [show canonDeForm (localColim s₀) (BoundedFormulaω.iInf φs) g
        = BoundedFormulaω.iInf (fun i => canonDeForm (localColim s₀) (φs i) g) from rfl,
      BoundedFormulaω.realize_iInf] at hd
    exact hd

/-- **The packaged corollary** (the milestone): the schema-template Ω-witness property + tail
indiscernibility deliver `OmegaCompleteForColim` for any `LocalEMContext` whose sequence is the
schema sequence, by composing the normal-form bridge with the existing reduction theorem. This
is exactly the hard input `tailTemplateRealizable_of_localEMContext` consumes. -/
theorem TailTemplateOmegaWitnessed.omegaCompleteForColim {J : Type} [LinearOrder J] {a : ℕ → M}
    (hTail : IsLomega1omegaIndiscernibleOnTail (L := localColim s₀) a (ΓEMlocal s₀))
    (h : TailTemplateOmegaWitnessed s₀ a) (ctx : LocalEMContext (localColim s₀) J (M := M))
    (hctxa : ctx.a = a) : LocalEMContext.OmegaCompleteForColim s₀ J ctx := by
  subst hctxa
  exact LocalEMContext.omegaCompleteForColim_of_omegaHomogeneous s₀ J ctx
    (h.to_localEMOmegaHomogeneous hTail)

end FirstOrder.Language
