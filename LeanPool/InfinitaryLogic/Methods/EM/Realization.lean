/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.EM.Template
import LeanPool.InfinitaryLogic.Methods.Henkin.Construction
import Mathlib.Data.Finset.Sort

/-!
# Template-to-`L[[J]]`-theory bridge for Lω₁ω

For each Lω₁ω template `T : Lomega1omegaTemplate L` and each linearly ordered
index type `J`, this file builds the set of `L[[J]]`-sentences whose models are
exactly the `L[[J]]`-structures whose constants realize `T`. The bridge
consists of:

- `templateSentence φ t`: the `L[[J]]`-sentence "`φ` holds on the constants
  indexed by the increasing tuple `t : Fin n ↪o J`".
- `realize_templateSentence`: the semantic bridge — realizing
  `templateSentence φ t` in an `L[[J]]`-expansion of an `L`-structure `M`
  (built from a function `σ : J → M`) is equivalent to realizing the
  underlying Lω₁ω formula `φ` on the tuple `σ ∘ t`.
- `templateTheory T J`: the set of `L[[J]]`-sentences obtained by including,
  for each `(n, φ, t)`, either `templateSentence φ t` (if `T.truth φ`) or its
  negation (if `¬ T.truth φ`).
- `IsLomega1omegaIndiscernible.templateTheory_finitelySatisfiable`: when the
  template comes from an indiscernible sequence indexed by an infinite linear
  order, every finite subset of the resulting template theory is satisfiable
  in the source model.

This file does **not** turn the template into a single model — that step is
blocked both by uncountable `J` (the language `L[[J]]` has uncountably many
constant symbols) and, even for countable `J`, by the fact that `templateTheory T J`
inherits the continuum size of the Lω₁ω formula syntax. Any future
model-realizing tranche will need to restrict to a countable sub-theory.
-/

universe u v w

namespace FirstOrder.Language

variable {L : Language.{u, v}}

/-! ### Section 1: a `Fin n` order-embedding into any infinite linear order -/

/-- Any infinite linear order admits a strictly-increasing tuple of every
finite length. Constructed by sorting `n` distinct elements obtained from
`Infinite.natEmbedding`. -/
private theorem Fin.exists_orderEmbedding_of_infinite
    {I : Type*} [LinearOrder I] [Infinite I] (n : ℕ) :
    Nonempty (Fin n ↪o I) := by
  classical
  let f : ℕ ↪ I := Infinite.natEmbedding I
  let s : Finset I := (Finset.range n).image f
  have hcard : s.card = n := by
    rw [Finset.card_image_of_injective _ f.injective, Finset.card_range]
  exact ⟨s.orderEmbOfFin hcard⟩

/-- `Fin n ↪o J` is countable whenever `J` is countable. The injection from
`Fin n ↪o J` to `Fin n → J` via `DFunLike.coe` is injective (by
`DFunLike.coe_injective`), and `Fin n → J` is countable when `J` is countable
because `Fin n` is finite. -/
private theorem Fin.countable_orderEmbedding (n : ℕ) {J : Type*} [LinearOrder J]
    [Countable J] : Countable (Fin n ↪o J) :=
  Function.Injective.countable
    (f := fun e : Fin n ↪o J => (⇑e : Fin n → J))
    (fun _ _ h => DFunLike.coe_injective h)

/-! ### Section 2: `templateSentence` — the L[[J]]-sentence "φ on the constants of `t`" -/

namespace Lomega1omegaTemplate

variable {J : Type u} [LinearOrder J]

/-- The `L[[J]]`-sentence expressing "`φ` holds when its `n` bound variables are
interpreted as the constants `c_{t 0}, …, c_{t (n-1)}`". Built by lifting `φ`
to `L[[J]]`, opening its bound variables, and substituting them with the
closed terms for the constants `t 0, …, t (n-1)`. -/
def templateSentence
    {n : ℕ} (φ : L.BoundedFormulaω Empty n) (t : Fin n ↪o J) :
    L[[J]].Sentenceω :=
  let φ' : L[[J]].BoundedFormulaω Empty n := φ.mapLanguage (L.lhomWithConstants J)
  let φ'' : L[[J]].Formulaω (Fin n) := φ'.openBounds
  let tf : Fin n → L[[J]].Term Empty :=
    fun i => Term.func (Sum.inr (t i) : L[[J]].Functions 0) Fin.elim0
  φ''.subst tf

end Lomega1omegaTemplate

/-! ### Section 3: `realize_templateSentence` — semantic bridge to `φ.Realize` -/

/-- Realizing `templateSentence φ t` in an `L[[J]]`-expansion of `M` (built from
a function `σ : J → M` via `constantsOn.structure σ`) is equivalent to realizing
`φ` itself on the tuple `σ ∘ t : Fin n → M`. The proof composes
`realize_subst`, `realize_openBounds`, and `realize_mapLanguage`. -/
theorem realize_templateSentence
    {M : Type*} [L.Structure M]
    {J : Type u} [LinearOrder J] (σ : J → M)
    {n : ℕ} (φ : L.BoundedFormulaω Empty n) (t : Fin n ↪o J) :
    letI : (constantsOn J).Structure M := constantsOn.structure σ
    Sentenceω.Realize (Lomega1omegaTemplate.templateSentence φ t) M ↔
      φ.Realize (Empty.elim : Empty → M) (σ ∘ t) := by
  let : (constantsOn J).Structure M := constantsOn.structure σ
  -- Unfold templateSentence and Sentenceω.Realize
  show BoundedFormulaω.Realize _ Empty.elim Fin.elim0 ↔ _
  rw [Lomega1omegaTemplate.templateSentence, BoundedFormulaω.realize_subst]
  -- The substituted function is definitionally `σ ∘ t` because each constant
  -- term `Sum.inr (t i)` evaluates to `σ (t i)` via `constantsOn.structure σ`.
  -- Now we need to dispose of the `openBounds` and `mapLanguage` layers.
  -- After realize_subst, the goal is:
  --   BoundedFormulaω.Realize ((φ.mapLanguage _).openBounds) (σ ∘ t) Fin.elim0 ↔
  --     φ.Realize Empty.elim (σ ∘ t)
  -- which equals (definitionally) Formulaω.Realize ((φ.mapLanguage _).openBounds) (σ ∘ t).
  exact (realize_openBounds _ _).trans
        (BoundedFormulaω.realize_mapLanguage _ _ _ _)

/-! ### Section 4: `templateTheory` — the L[[J]]-theory pinning down the template -/

namespace Lomega1omegaTemplate

variable {J : Type u} [LinearOrder J]

/-- The `L[[J]]`-theory whose models are exactly the `L[[J]]`-structures whose
constants realize the template `T`. For each formula `φ` and each increasing
tuple `t : Fin n ↪o J`, the theory contains either `templateSentence φ t` (if
`T.truth φ`) or its negation (if `¬ T.truth φ`). Both directions are needed:
without the negative sentences, a model could realize formulas the template
declares false. -/
private def templateTheory (T : Lomega1omegaTemplate L) (J : Type u) [LinearOrder J] :
    Set L[[J]].Sentenceω :=
  { σ : L[[J]].Sentenceω |
      ∃ (n : ℕ) (φ : L.BoundedFormulaω Empty n) (t : Fin n ↪o J),
        (T.truth φ ∧ σ = templateSentence φ t) ∨
        (¬ T.truth φ ∧ σ = (templateSentence φ t).not) }

/-- The restricted template theory: like `templateTheory`, but only includes
sentences for formulas whose `(arity, φ)`-pair lies in the family `Γ`. When
`Γ` and `J` are both countable, the resulting theory is countable (see
`templateTheoryOn_countable`), making it a candidate input to
`model_existence` — which the full `templateTheory` can never be. -/
def templateTheoryOn
    (T : Lomega1omegaTemplate L)
    (Γ : Set (Σ n, L.BoundedFormulaω Empty n))
    (J : Type u) [LinearOrder J] :
    Set L[[J]].Sentenceω :=
  { σ : L[[J]].Sentenceω |
      ∃ (n : ℕ) (φ : L.BoundedFormulaω Empty n) (t : Fin n ↪o J),
        ⟨n, φ⟩ ∈ Γ ∧
        ((T.truth φ ∧ σ = templateSentence φ t) ∨
         (¬ T.truth φ ∧ σ = (templateSentence φ t).not)) }

/-- Monotonicity: the restricted template theory is a subset of the full
template theory. -/
private theorem templateTheoryOn_subset_templateTheory
    (T : Lomega1omegaTemplate L)
    (Γ : Set (Σ n, L.BoundedFormulaω Empty n))
    (J : Type u) [LinearOrder J] :
    T.templateTheoryOn Γ J ⊆ T.templateTheory J := by
  rintro σ ⟨n, φ, t, _hΓ, hcase⟩
  exact ⟨n, φ, t, hcase⟩



/-- When the family `Γ` and the index type `J` are both countable, the
restricted template theory is countable. This is the point of `templateTheoryOn`:
the full `templateTheory T J` is always continuum-sized (Lω₁ω formulas form a
continuum), but the restricted theory can be countable and thus a candidate
input to `model_existence`. -/
private theorem templateTheoryOn_countable
    {T : Lomega1omegaTemplate L}
    {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} (hΓ : Γ.Countable)
    {J : Type u} [LinearOrder J] [Countable J] :
    (T.templateTheoryOn Γ J).Countable := by
  classical
  have : Countable ↥Γ := hΓ.to_subtype
  have : ∀ n : ℕ, Countable (Fin n ↪o J) := fun n => Fin.countable_orderEmbedding n
  have : Countable (Σ x : ↥Γ, Fin x.val.1 ↪o J) := inferInstance
  refine (Set.countable_range (fun p : Σ x : ↥Γ, Fin x.val.1 ↪o J =>
    if T.truth p.1.val.2 then templateSentence p.1.val.2 p.2
    else (templateSentence p.1.val.2 p.2).not)).mono ?_
  rintro σ ⟨n, φ, t, hΓφ, hcase⟩
  refine ⟨⟨⟨⟨n, φ⟩, hΓφ⟩, t⟩, ?_⟩
  rcases hcase with ⟨hpos, heq⟩ | ⟨hneg, heq⟩
  · simp only [ite_eq_left hpos]
    exact heq.symm
  · simp only [ite_eq_right hneg]
    exact heq.symm

end Lomega1omegaTemplate

/-! ### Section 5: finite satisfiability of `templateTheory` in the source model -/

/-- If `h : IsLomega1omegaIndiscernible a` for `a : I → M` over an infinite linear
order `I`, then every finite subset of `templateTheory h.template J` is
satisfiable in the source model `M`, expanded to an `L[[J]]`-structure via an
appropriate interpretation `σ : J → M`. The interpretation is built by sorting
the finitely many J-indices appearing in the finite fragment, embedding them
into `I` via `[Infinite I]`, and pulling them through `a`. -/
private theorem IsLomega1omegaIndiscernible.templateTheory_finitelySatisfiable
    {I : Type w} [LinearOrder I] [Infinite I]
    {M : Type*} [L.Structure M] {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {J : Type u} [LinearOrder J]
    {F : Set L[[J]].Sentenceω}
    (hFin : F.Finite) (hSub : F ⊆ h.template.templateTheory J) :
    ∃ σ : J → M,
      letI : (constantsOn J).Structure M := constantsOn.structure σ
      ∀ τ ∈ F, Sentenceω.Realize τ M := by
  classical
  -- Step 1: pick a base point i₀ ∈ I, m₀ := a i₀ ∈ M
  have : Nonempty I := inferInstance
  let i₀ : I := Classical.arbitrary I
  let m₀ : M := a i₀
  -- Step 2: extract witnesses for each τ ∈ F
  -- Each τ ∈ F is in templateTheory, giving (n_τ, φ_τ, t_τ) and a sign disjunction.
  have witness : ∀ τ : F, ∃ (n : ℕ) (φ : L.BoundedFormulaω Empty n) (t : Fin n ↪o J),
      (h.template.truth φ ∧ (τ : L[[J]].Sentenceω) = Lomega1omegaTemplate.templateSentence φ t) ∨
      (¬ h.template.truth φ ∧
        (τ : L[[J]].Sentenceω) = (Lomega1omegaTemplate.templateSentence φ t).not) :=
    fun τ => hSub τ.property
  choose nOf phiOf tOf hOf using witness
  -- Step 3: collect mentioned J-indices into a finset and sort
  have : Fintype ↥F := hFin.fintype
  let S : Finset J := (Finset.univ : Finset ↥F).biUnion
    (fun τ => (Finset.univ : Finset (Fin (nOf τ))).image (fun i => tOf τ i))
  let k : ℕ := S.card
  let orderIso : Fin k ≃o ↥S := S.orderIsoOfFin rfl
  obtain ⟨f⟩ := Fin.exists_orderEmbedding_of_infinite (I := I) k
  -- Step 4: define σ : J → M, piecewise on membership in S
  let σ : J → M := fun j =>
    if hj : j ∈ S then a (f (orderIso.symm ⟨j, hj⟩)) else m₀
  refine ⟨σ, ?_⟩
  let : (constantsOn J).Structure M := constantsOn.structure σ
  -- Step 5: verify each τ ∈ F realizes
  -- Helper: every value of every t_τ lies in S
  have htS : ∀ (τ : ↥F) (i : Fin (nOf τ)), tOf τ i ∈ S := by
    intro τ i
    exact Finset.mem_biUnion.mpr ⟨τ, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  -- Helper: for each τ, the factorization t'_τ : Fin (nOf τ) → Fin k
  let t'Of : ∀ (τ : ↥F), Fin (nOf τ) → Fin k :=
    fun τ i => orderIso.symm ⟨tOf τ i, htS τ i⟩
  -- t'Of τ is strictly monotone
  have t'Of_strictMono : ∀ (τ : ↥F), StrictMono (t'Of τ) := by
    intro τ i j hij
    have h1 : (tOf τ i : J) < tOf τ j := (tOf τ).strictMono hij
    show orderIso.symm ⟨tOf τ i, htS τ i⟩ < orderIso.symm ⟨tOf τ j, htS τ j⟩
    rw [orderIso.symm.lt_iff_lt]
    exact h1
  -- f ∘ t'Of τ : Fin (nOf τ) → I is strictly monotone
  have ft'_strictMono : ∀ (τ : ↥F), StrictMono (fun i => f (t'Of τ i)) :=
    fun τ => f.strictMono.comp (t'Of_strictMono τ)
  -- σ ∘ tOf τ = a ∘ (f ∘ t'Of τ) as functions Fin (nOf τ) → M
  have sigma_eq : ∀ (τ : ↥F),
      (σ ∘ (fun i => tOf τ i) : Fin (nOf τ) → M) =
      (fun i => a (f (t'Of τ i))) := by
    intro τ
    funext i
    show σ (tOf τ i) = a (f (t'Of τ i))
    show (if hj : tOf τ i ∈ S then a (f (orderIso.symm ⟨tOf τ i, hj⟩)) else m₀) =
         a (f (orderIso.symm ⟨tOf τ i, htS τ i⟩))
    rw [dite_eq_left (htS τ i)]
  -- Now verify each τ ∈ F
  intro τ hτ
  let τ' : ↥F := ⟨τ, hτ⟩
  show Sentenceω.Realize (↑τ' : L[[J]].Sentenceω) M
  rcases hOf τ' with ⟨hpos, heq⟩ | ⟨hneg, heq⟩
  · -- positive case: τ = templateSentence (phiOf τ') (tOf τ')
    rw [heq, realize_templateSentence σ (phiOf τ') (tOf τ')]
    -- Goal: (phiOf τ').Realize Empty.elim (σ ∘ tOf τ')
    rw [show (σ ∘ ⇑(tOf τ') : Fin (nOf τ') → M) = (fun i => a (f (t'Of τ' i))) from
        sigma_eq τ']
    -- Goal: (phiOf τ').Realize Empty.elim (fun i => a (f (t'Of τ' i)))
    -- which equals (a ∘ (f ∘ t'Of τ'))
    show (phiOf τ').Realize (Empty.elim : Empty → M) (a ∘ (fun i => f (t'Of τ' i)))
    exact (h.template_truth_iff (phiOf τ') (ft'_strictMono τ')).mp hpos
  · -- negative case: τ = (templateSentence (phiOf τ') (tOf τ')).not
    rw [heq]
    show ¬ Sentenceω.Realize (Lomega1omegaTemplate.templateSentence (phiOf τ') (tOf τ')) M
    rw [realize_templateSentence σ (phiOf τ') (tOf τ')]
    rw [show (σ ∘ ⇑(tOf τ') : Fin (nOf τ') → M) = (fun i => a (f (t'Of τ' i))) from
        sigma_eq τ']
    show ¬ (phiOf τ').Realize (Empty.elim : Empty → M) (a ∘ (fun i => f (t'Of τ' i)))
    intro hrealize
    apply hneg
    exact (h.template_truth_iff (phiOf τ') (ft'_strictMono τ')).mpr hrealize

/-- Restricted-indiscernibility variant of `templateTheory_finitelySatisfiable`:
every finite subset of `(templateOfSeq a).templateTheoryOn Γ J` is
satisfiable in the source model, provided `a` is restricted-indiscernible
on `Γ` (not on all formulas).

This is a **fresh specialized proof**, not a delegation through the
full-indiscernibility version: the witness extraction explicitly carries
`⟨n, φ⟩ ∈ Γ` so that the weaker `templateOfSeq_truth_iff` applies at
the final step. The `σ`/Finset plumbing is identical to the full version
at lines 208-295; only the witness-extraction step (Step 2) and the
final `template_truth_iff` calls (Step 5) differ. -/
theorem IsLomega1omegaIndiscernibleOn.templateTheoryOn_finitelySatisfiable
    {I : Type w} [LinearOrder I] [Infinite I]
    {M : Type*} [L.Structure M] {a : I → M}
    {Γ : Set (Σ n, L.BoundedFormulaω Empty n)}
    (h : IsLomega1omegaIndiscernibleOn (L := L) a Γ)
    {J : Type u} [LinearOrder J]
    {F : Set L[[J]].Sentenceω}
    (hFin : F.Finite) (hSub : F ⊆ (templateOfSeq (L := L) a).templateTheoryOn Γ J) :
    ∃ σ : J → M,
      letI : (constantsOn J).Structure M := constantsOn.structure σ
      ∀ τ ∈ F, Sentenceω.Realize τ M := by
  classical
  have : Nonempty I := inferInstance
  let i₀ : I := Classical.arbitrary I
  let m₀ : M := a i₀
  -- Step 2 (modified): extract witnesses carrying membership in Γ.
  have witness : ∀ τ : F, ∃ (n : ℕ) (φ : L.BoundedFormulaω Empty n)
      (t : Fin n ↪o J), ⟨n, φ⟩ ∈ Γ ∧
      (((templateOfSeq (L := L) a).truth φ ∧
        (τ : L[[J]].Sentenceω) = Lomega1omegaTemplate.templateSentence φ t) ∨
       (¬ (templateOfSeq (L := L) a).truth φ ∧
        (τ : L[[J]].Sentenceω) = (Lomega1omegaTemplate.templateSentence φ t).not)) := by
    intro τ
    obtain ⟨n, φ, t, hΓmem, hcase⟩ := hSub τ.property
    exact ⟨n, φ, t, hΓmem, hcase⟩
  choose nOf phiOf tOf hΓOf hOf using witness
  have : Fintype ↥F := hFin.fintype
  let S : Finset J := (Finset.univ : Finset ↥F).biUnion
    (fun τ => (Finset.univ : Finset (Fin (nOf τ))).image (fun i => tOf τ i))
  let k : ℕ := S.card
  let orderIso : Fin k ≃o ↥S := S.orderIsoOfFin rfl
  obtain ⟨f⟩ := Fin.exists_orderEmbedding_of_infinite (I := I) k
  let σ : J → M := fun j =>
    if hj : j ∈ S then a (f (orderIso.symm ⟨j, hj⟩)) else m₀
  refine ⟨σ, ?_⟩
  let : (constantsOn J).Structure M := constantsOn.structure σ
  have htS : ∀ (τ : ↥F) (i : Fin (nOf τ)), tOf τ i ∈ S := by
    intro τ i
    exact Finset.mem_biUnion.mpr ⟨τ, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let t'Of : ∀ (τ : ↥F), Fin (nOf τ) → Fin k :=
    fun τ i => orderIso.symm ⟨tOf τ i, htS τ i⟩
  have t'Of_strictMono : ∀ (τ : ↥F), StrictMono (t'Of τ) := by
    intro τ i j hij
    have h1 : (tOf τ i : J) < tOf τ j := (tOf τ).strictMono hij
    show orderIso.symm ⟨tOf τ i, htS τ i⟩ < orderIso.symm ⟨tOf τ j, htS τ j⟩
    rw [orderIso.symm.lt_iff_lt]
    exact h1
  have ft'_strictMono : ∀ (τ : ↥F), StrictMono (fun i => f (t'Of τ i)) :=
    fun τ => f.strictMono.comp (t'Of_strictMono τ)
  have sigma_eq : ∀ (τ : ↥F),
      (σ ∘ (fun i => tOf τ i) : Fin (nOf τ) → M) =
      (fun i => a (f (t'Of τ i))) := by
    intro τ
    funext i
    show σ (tOf τ i) = a (f (t'Of τ i))
    show (if hj : tOf τ i ∈ S then a (f (orderIso.symm ⟨tOf τ i, hj⟩)) else m₀) =
         a (f (orderIso.symm ⟨tOf τ i, htS τ i⟩))
    rw [dite_eq_left (htS τ i)]
  intro τ hτ
  let τ' : ↥F := ⟨τ, hτ⟩
  show Sentenceω.Realize (↑τ' : L[[J]].Sentenceω) M
  rcases hOf τ' with ⟨hpos, heq⟩ | ⟨hneg, heq⟩
  · rw [heq, realize_templateSentence σ (phiOf τ') (tOf τ')]
    rw [show (σ ∘ ⇑(tOf τ') : Fin (nOf τ') → M) = (fun i => a (f (t'Of τ' i))) from
        sigma_eq τ']
    show (phiOf τ').Realize (Empty.elim : Empty → M) (a ∘ (fun i => f (t'Of τ' i)))
    exact (h.templateOfSeq_truth_iff (hΓOf τ') (ft'_strictMono τ')).mp hpos
  · rw [heq]
    show ¬ Sentenceω.Realize (Lomega1omegaTemplate.templateSentence (phiOf τ') (tOf τ')) M
    rw [realize_templateSentence σ (phiOf τ') (tOf τ')]
    rw [show (σ ∘ ⇑(tOf τ') : Fin (nOf τ') → M) = (fun i => a (f (t'Of τ' i))) from
        sigma_eq τ']
    show ¬ (phiOf τ').Realize (Empty.elim : Empty → M) (a ∘ (fun i => f (t'Of τ' i)))
    intro hrealize
    apply hneg
    exact (h.templateOfSeq_truth_iff (hΓOf τ') (ft'_strictMono τ')).mpr hrealize

/-- Restricted version of `templateTheory_finitelySatisfiable`: every finite
subset of `h.template.templateTheoryOn Γ J` is satisfiable in the source model.
This is a direct corollary via `templateTheoryOn_subset_templateTheory`; the
point of stating it separately is that this is the form a downstream
model-existence call will actually invoke (since only the restricted theory
can ever be countable). -/
theorem IsLomega1omegaIndiscernible.templateTheoryOn_finitelySatisfiable
    {I : Type w} [LinearOrder I] [Infinite I]
    {M : Type*} [L.Structure M] {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {J : Type u} [LinearOrder J]
    (Γ : Set (Σ n, L.BoundedFormulaω Empty n))
    {F : Set L[[J]].Sentenceω}
    (hFin : F.Finite) (hSub : F ⊆ h.template.templateTheoryOn Γ J) :
    ∃ σ : J → M,
      letI : (constantsOn J).Structure M := constantsOn.structure σ
      ∀ τ ∈ F, Sentenceω.Realize τ M :=
  h.templateTheory_finitelySatisfiable hFin
    (hSub.trans (Lomega1omegaTemplate.templateTheoryOn_subset_templateTheory _ Γ J))

-- Admissible/Barwise adapter theorems (_of_fragment, _of_fullFragment,
-- _of_compact) have been moved to Methods/EM/FragmentAdapter.lean to keep
-- the Countable bundle free of admissible-fragment imports.

/-! ### Section 7: sequence-indexed wrappers

Convenience wrappers over `templateTheoryOn` specialized to a family given as a
sequence `s : ℕ → Σ n, L.BoundedFormulaω Empty n`. The payoff is ergonomic: the
countability of `Set.range s` is automatic, so `templateTheoryOfSeq_countable`
drops the `Γ.Countable` hypothesis that `templateTheoryOn_countable` requires. -/

namespace Lomega1omegaTemplate

variable {J : Type u} [LinearOrder J]

/-- Sequence-based restricted template theory: same content as
`templateTheoryOn T (Set.range s) J`, with a dedicated name for callers that
want to hand a sequence rather than a set. -/
def templateTheoryOfSeq
    (T : Lomega1omegaTemplate L)
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    (J : Type u) [LinearOrder J] :
    Set L[[J]].Sentenceω :=
  T.templateTheoryOn (Set.range s) J

/-- `templateTheoryOfSeq` is countable whenever `J` is countable. Follows from
`templateTheoryOn_countable` via `Set.countable_range`; the countability of the
family comes for free from the sequence structure. -/
private theorem templateTheoryOfSeq_countable
    {T : Lomega1omegaTemplate L}
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    [Countable J] :
    (T.templateTheoryOfSeq s J).Countable :=
  templateTheoryOn_countable (Set.countable_range s)

end Lomega1omegaTemplate

/-- Sequence-indexed finite satisfiability in the source indiscernible model.
Direct delegation to `templateTheoryOn_finitelySatisfiable`. -/
theorem IsLomega1omegaIndiscernible.templateTheoryOfSeq_finitelySatisfiable
    {I : Type w} [LinearOrder I] [Infinite I]
    {M : Type*} [L.Structure M] {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {J : Type u} [LinearOrder J]
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    {F : Set L[[J]].Sentenceω}
    (hFin : F.Finite) (hSub : F ⊆ h.template.templateTheoryOfSeq s J) :
    ∃ σ : J → M,
      letI : (constantsOn J).Structure M := constantsOn.structure σ
      ∀ τ ∈ F, Sentenceω.Realize τ M :=
  h.templateTheoryOn_finitelySatisfiable (Set.range s) hFin hSub

-- Admissible/Barwise adapter theorems for the seq API (_of_fragment,
-- _of_fullFragment, _of_compact) are in Methods/EM/FragmentAdapter.lean.

/-- Sequence-indexed wrapper for `templateTheoryOn_finitelySatisfiable`
under restricted indiscernibility. -/
theorem IsLomega1omegaIndiscernibleOn.templateTheoryOfSeq_finitelySatisfiable
    {I : Type w} [LinearOrder I] [Infinite I]
    {M : Type*} [L.Structure M] {a : I → M}
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    (h : IsLomega1omegaIndiscernibleOn (L := L) a (Set.range s))
    {J : Type u} [LinearOrder J]
    {F : Set L[[J]].Sentenceω}
    (hFin : F.Finite)
    (hSub : F ⊆ (templateOfSeq (L := L) a).templateTheoryOfSeq s J) :
    ∃ σ : J → M,
      letI : (constantsOn J).Structure M := constantsOn.structure σ
      ∀ τ ∈ F, Sentenceω.Realize τ M :=
  h.templateTheoryOn_finitelySatisfiable hFin hSub

end FirstOrder.Language
