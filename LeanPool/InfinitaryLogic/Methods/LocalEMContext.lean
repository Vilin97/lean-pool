/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LocalEMFamily
import LeanPool.InfinitaryLogic.Methods.Henkin.Construction
import LeanPool.InfinitaryLogic.Methods.TailIndiscernible
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite

/-!
# The local EM context, layer 1: deep interpretation and realize bridges

The semantic layer of the `EMContext` re-base, **generic over `Λ`**: the deep interpretation of
closed `Λ[[J]]`-terms in a source model and the realize bridges connecting it to the syntactic
de-substitution pipeline of `LocalEMFamily.lean`. Mirrors the `skolemColim`-specific chain of
`EMTermModel.lean`, with one systematic simplification: every original proof touched the language
structure only through `letI := skolemColimStructure L`, so here the structure is simply the
ambient instance `[Λ.Structure M]` — `localColimStructure` enters only at instantiation sites
(as in `LocalEMExtraction.lean`). No `[Nonempty M]` is needed (no Hilbert choice in this layer).

Contents (source lemma in `EMTermModel.lean` in parentheses):
* `locDeepInterp` (`deepInterp`) + `locDeepInterp_func`, and the realization bridges
  `locDeepInterp_eq_realize`, `locDeepInterp_subst`, `locDeepInterp_onTerm_subst`;
* the support bridge `locJSupport_onTerm_subst_subset` (`jSupport_onTerm_subst_subset`);
* the ordered-position/`Fin`-arity bridges `locDeepInterp_eq_realize_pos`,
  `locDeTermFin_realize` (`deepInterp_eq_realize_fin`), and the **superset realization
  invariance** `locDeTermFin_realize_superset`;
* the atom bridges `realize_locDeEqAtom(_superset)`, `realize_locDeRelAtom(_superset)` — the
  superset variants route through `locDeTermFin_realize_superset` instead of re-deriving the
  per-term key inline as the originals do;
* the general formula bridge `realize_locDeForm` (`realize_deForm`), consuming
  `realize_openBounds` (imported explicitly from `Methods/Henkin/Construction.lean`) and
  `realize_relabel_sumInr_zero` (from the `Lomega1omega` core).

This file also carries the generic quotient layer: `locDeepInterp_snoc`, the eventual-equality
relation `LocalEMEq` (refl/symm) with its support-enlargement engine
(`LocalEMEq_eventually_on_superset`, `eventually_locDeepInterp_superset_iff`,
`eventually_locRelMap_superset_iff`), the `LocalEMContext` standing-data structure, and (in the
`Quotient` section) the carrier + `Λ[[J]]`-`Structure`. The tail-indiscernibility predicate
`IsLomega1omegaIndiscernibleOnTail` comes from the neutral `Methods/TailIndiscernible.lean`, so this
file stays EM-free.

Next layers (subsequent chunks): the `skolemNeedSymbol` witness-term transport and the
family-membership-carrying restricted truth lemma.
-/

namespace FirstOrder.Language

variable (Λ : Language.{0, 0}) (J : Type) [LinearOrder J]

/-! ### Support of substituted base-language terms (syntactic) -/

/-- **Support of a base-language term after substitution**: substituting the closed terms `ts`
for the free variables of a base-language term `(onTerm t)` (which itself carries no
`J`-constants, being a `Λ`-image) produces only the `J`-constants of the `ts`. The bridge from a
uniform support hypothesis `S ⊇ ⋃ locJSupport (ts i)` to the per-atom support hypotheses of the
congruence layer. -/
theorem locJSupport_onTerm_subst_subset {n : ℕ} (t : Λ.Term (Empty ⊕ Fin n))
    (ts : Fin n → Λ[[J]].Term Empty) :
    locJSupport Λ J (((lhomWithConstants Λ J).onTerm t).subst (Sum.elim (fun e => e.elim) ts))
      ⊆ Finset.univ.biUnion fun i => locJSupport Λ J (ts i) := by
  induction t with
  | var x =>
    cases x with
    | inl e => exact e.elim
    | inr i =>
      exact Finset.subset_biUnion_of_mem (fun i => locJSupport Λ J (ts i)) (Finset.mem_univ i)
  | @func l f args ih =>
    have hjc : locJConstOf Λ J ((lhomWithConstants Λ J).onFunction f) = ∅ := by
      cases l <;> rfl
    change locJSupport Λ J (Term.func ((lhomWithConstants Λ J).onFunction f) _) ⊆ _
    rw [locJSupport, hjc, Finset.union_empty]
    exact Finset.biUnion_subset.mpr fun i _ => ih i

/-! ### Deep interpretation -/

section DeepInterp

variable {M : Type} [Λ.Structure M] (a : ℕ → M)

/-- The **deep interpretation** of a closed `Λ[[J]]`-term at depth `d` relative to a support `S`:
interpret each `J`-constant `c_j` by the source sequence at position `d + deepRank S j` (so
support constants map to a strictly-increasing deep tuple of `a`), and evaluate in `M`'s ambient
`Λ`-structure. -/
noncomputable def locDeepInterp (d : ℕ) (S : Finset J) (t : Λ[[J]].Term Empty) : M :=
  letI : (constantsOn J).Structure M := constantsOn.structure (fun j => a (d + deepRank J S j))
  t.realize Empty.elim

/-- Deep interpretation commutes with function application (same depth and support): it is the
structure's `funMap` of the argument interpretations. Immediate from `Term.realize`. -/
theorem locDeepInterp_func (d : ℕ) (S : Finset J) {n : ℕ}
    (f : Λ[[J]].Functions n) (ts : Fin n → Λ[[J]].Term Empty) :
    locDeepInterp Λ J a d S (.func f ts) =
      letI : (constantsOn J).Structure M := constantsOn.structure (fun j => a (d + deepRank J S j))
      Structure.funMap f (fun i => locDeepInterp Λ J a d S (ts i)) :=
  rfl

/-- **De-substitution bridge**: the deep interpretation of a closed term equals the
*de-substituted* `Λ`-term `constantsToVars t` (each skeleton constant `c_j` turned into the
variable `Sum.inl j`) realized with `j ↦ a (d + deepRank S j)`. Turns the support machinery from
combinatorial into semantic — the right-hand side is a genuine formula realization, so tail
indiscernibility applies. -/
theorem locDeepInterp_eq_realize (d : ℕ) (S : Finset J) (t : Λ[[J]].Term Empty) :
    locDeepInterp Λ J a d S t =
      t.constantsToVars.realize (Sum.elim (fun j => a (d + deepRank J S j)) Empty.elim) := by
  let : (constantsOn J).Structure M := constantsOn.structure (fun j => a (d + deepRank J S j))
  change t.realize Empty.elim = _
  exact (Term.realize_constantsToVars (t := t) (v := Empty.elim)).symm

/-- **M-side term substitution**: the deep interpretation of a substituted term is the
realization (in `M`'s `[[J]]`-structure at depth `d`) of the body on the deep interpretations of
the substituted terms. Mostly `Term.realize_subst` (deep interpretation *is* realization in the
depth-`d` structure). -/
private theorem locDeepInterp_subst (d : ℕ) (S : Finset J) {n : ℕ}
    (t : Λ[[J]].Term (Empty ⊕ Fin n)) (ts : Fin n → Λ[[J]].Term Empty) :
    letI : (constantsOn J).Structure M := constantsOn.structure fun j => a (d + deepRank J S j)
    locDeepInterp Λ J a d S (t.subst (Sum.elim (fun e => e.elim) ts)) =
      t.realize (Sum.elim Empty.elim fun i => locDeepInterp Λ J a d S (ts i)) := by
  let : (constantsOn J).Structure M := constantsOn.structure fun j => a (d + deepRank J S j)
  change (t.subst (Sum.elim (fun e => e.elim) ts)).realize Empty.elim = _
  rw [Term.realize_subst]
  congr 1
  funext x
  cases x with
  | inl e => exact e.elim
  | inr i => rfl

/-- **Deep interpretation of a base-language substituted term**: combining `locDeepInterp_subst`
with `realize_onTerm`, the deep interpretation of `(onTerm t).subst ts` equals `t` realized in
`M`'s ambient `Λ`-structure on the deep interpretations of the substituted terms. -/
theorem locDeepInterp_onTerm_subst (d : ℕ) (S : Finset J) {n : ℕ}
    (t : Λ.Term (Empty ⊕ Fin n)) (ts : Fin n → Λ[[J]].Term Empty) :
    locDeepInterp Λ J a d S
        (((lhomWithConstants Λ J).onTerm t).subst (Sum.elim (fun e => e.elim) ts)) =
      t.realize (Sum.elim Empty.elim fun i => locDeepInterp Λ J a d S (ts i)) := by
  let : (constantsOn J).Structure M := constantsOn.structure fun j => a (d + deepRank J S j)
  rw [locDeepInterp_subst]
  exact LHom.realize_onTerm (lhomWithConstants Λ J) t _

/-! ### Ordered-position and `Fin`-arity realize bridges -/

/-- **Ordered-position realize bridge**: the deep interpretation is the realize of the
ordered-position de-substituted term on the *consecutive* deep tuple `n ↦ a (d + n)` — exactly
the shape tail indiscernibility consumes (a strictly-increasing deep tuple). -/
private theorem locDeepInterp_eq_realize_pos (d : ℕ) (S : Finset J) (t : Λ[[J]].Term Empty) :
    locDeepInterp Λ J a d S t = (locDeTermPos Λ J S t).realize (fun n => a (d + n)) := by
  rw [locDeepInterp_eq_realize, locDeTermPos, Term.realize_relabel]
  congr 1
  funext x
  cases x with
  | inl j => rfl
  | inr e => exact e.elim

/-- **`Fin`-arity realize bridge**: the deep interpretation is the realize of the
`Fin S.card`-indexed de-substituted term on the consecutive deep tuple `i ↦ a (d + i)`, directly
feeding the atoms. -/
theorem locDeTermFin_realize (d : ℕ) (S : Finset J) (t : Λ[[J]].Term Empty)
    (hsub : locJSupport Λ J t ⊆ S) :
    locDeepInterp Λ J a d S t
      = (locDeTermFin Λ J S t hsub).realize (fun i : Fin S.card => a (d + i)) := by
  rw [locDeepInterp_eq_realize_pos, locDeTermFin]
  symm
  exact Term.realize_restrictVar (fun n => a (d + n)) (fun _ => rfl)

/-- **Superset realization invariance**: the `Fin`-arity de-substituted term over `S`, realized
on the `T`-induced deep tuple `i ↦ a (d + deepRank T (orderEmbOfFin S i))`, equals the deep
interpretation over the larger support `T`. The core shared by the equality- and relation-atom
superset bridges (restrictVar realize with a `dite`-extended assignment, then
`realize_eq_of_eq_on_varFinset` to discard the junk, then `orderEmbOfFin_deepRank`). -/
theorem locDeTermFin_realize_superset (d : ℕ) (S T : Finset J) (w : Λ[[J]].Term Empty)
    (hw : locJSupport Λ J w ⊆ S) :
    (locDeTermFin Λ J S w hw).realize
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i)))
      = locDeepInterp Λ J a d T w := by
  have hrv : (locDeTermFin Λ J S w hw).realize
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i)))
      = (locDeTermPos Λ J S w).realize
        (fun n => a (d + if h : n < S.card then deepRank J T (S.orderEmbOfFin rfl ⟨n, h⟩)
          else 0)) := by
    rw [locDeTermFin]
    refine Term.realize_restrictVar
      (fun n => a (d + if h : n < S.card then deepRank J T (S.orderEmbOfFin rfl ⟨n, h⟩) else 0))
      (fun x => ?_)
    simp only [dite_eq_left (Finset.mem_range.mp (locDeTermPos_varFinset_subset (Λ := Λ) (J
      := J) hw x.2))]
  rw [hrv, locDeepInterp_eq_realize, locDeTermPos, Term.realize_relabel]
  apply Term.realize_eq_of_eq_on_varFinset
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (locConstantsToVars_varFinset_subset Λ J w hx)
  have hjS : j ∈ S := hw hj
  have hlt : deepRank J S j < S.card := deepRank_lt_card (J := J) hjS
  have hdite : (if h : deepRank J S j < S.card then
      deepRank J T (S.orderEmbOfFin rfl ⟨deepRank J S j, h⟩) else 0) = deepRank J T j := by
    rw [dite_eq_left hlt, orderEmbOfFin_deepRank J S rfl hjS hlt]
  simp only [Function.comp_apply, Sum.elim_inl]
  exact congrArg (fun m => a (d + m)) hdite

/-! ### Atom and formula realize bridges -/

/-- **Equality-atom realize bridge**: the local de-substituted equality atom holds on the
consecutive deep tuple `i ↦ a (d + i)` iff `t` and `u` have equal deep interpretations at depth
`d` over `S`. -/
private theorem realize_locDeEqAtom (d : ℕ) (S : Finset J) (t u : Λ[[J]].Term Empty)
    (ht : locJSupport Λ J t ⊆ S) (hu : locJSupport Λ J u ⊆ S) :
    (locDeEqAtom Λ J S t u ht hu).Realize Empty.elim (fun i : Fin S.card => a (d + i)) ↔
      locDeepInterp Λ J a d S t = locDeepInterp Λ J a d S u := by
  rw [locDeEqAtom, canonEqAtom, BoundedFormulaω.realize_equal, Term.realize_relabel,
    Term.realize_relabel, Sum.elim_comp_inr, ← locDeTermFin_realize (t := t) (hsub := ht),
    ← locDeTermFin_realize (t := u) (hsub := hu)]

/-- **Superset equality-atom bridge**: the *same* atom over `S`, realized on the `T`-induced deep
tuple (`S ⊆ T`), holds iff `t` and `u` have equal deep interpretations over `T`. One
arity-`S.card` formula carries both the `S`-truth (consecutive tuple) and the `T`-truth (this
strictly-increasing tuple) — the input to tail indiscernibility. -/
private theorem realize_locDeEqAtom_superset (d : ℕ) {S T : Finset J} (_hST : S ⊆ T)
    (t u : Λ[[J]].Term Empty)
    (ht : locJSupport Λ J t ⊆ S) (hu : locJSupport Λ J u ⊆ S) :
    (locDeEqAtom Λ J S t u ht hu).Realize Empty.elim
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i))) ↔
      locDeepInterp Λ J a d T t = locDeepInterp Λ J a d T u := by
  rw [locDeEqAtom, canonEqAtom, BoundedFormulaω.realize_equal, Term.realize_relabel,
    Term.realize_relabel, Sum.elim_comp_inr,
    locDeTermFin_realize_superset (w := t) (hw := ht),
    locDeTermFin_realize_superset (w := u) (hw := hu)]

/-- **Relation-atom realize bridge**: the local de-substituted relation atom holds on the
consecutive deep tuple iff `R` holds in `M` on the deep interpretations over `S`. -/
private theorem realize_locDeRelAtom (d : ℕ) (S : Finset J) {l : ℕ} (R : Λ.Relations l)
    (ts : Fin l → Λ[[J]].Term Empty) (ht : ∀ i, locJSupport Λ J (ts i) ⊆ S) :
    (locDeRelAtom Λ J S R ts ht).Realize Empty.elim (fun i : Fin S.card => a (d + i)) ↔
      Structure.RelMap R fun i => locDeepInterp Λ J a d S (ts i) := by
  rw [locDeRelAtom, canonRelAtom, BoundedFormulaω.realize_rel]
  apply Iff.of_eq
  congr 1
  funext i
  rw [Term.realize_relabel, Sum.elim_comp_inr, ← locDeTermFin_realize]

/-- **Superset relation-atom bridge**: the same relation atom over `S`, realized on the
`T`-induced deep tuple (`S ⊆ T`), holds iff `R` holds in `M` on the deep interpretations over
`T`. Via `locDeTermFin_realize_superset`. -/
private theorem realize_locDeRelAtom_superset (d : ℕ) {S T : Finset J} (_hST : S ⊆ T) {l : ℕ}
    (R : Λ.Relations l) (ts : Fin l → Λ[[J]].Term Empty)
    (ht : ∀ i, locJSupport Λ J (ts i) ⊆ S) :
    (locDeRelAtom Λ J S R ts ht).Realize Empty.elim
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i))) ↔
      Structure.RelMap R fun i => locDeepInterp Λ J a d T (ts i) := by
  rw [locDeRelAtom, canonRelAtom, BoundedFormulaω.realize_rel]
  apply Iff.of_eq
  congr 1
  funext i
  rw [Term.realize_relabel, Sum.elim_comp_inr, locDeTermFin_realize_superset]

/-- **General formula realize bridge** (generalizes the atom bridges): the local de-substituted
formula holds on the consecutive deep tuple `i ↦ a (d + i)` iff `φ` holds in `M`'s ambient
`Λ`-structure on the deep interpretations of `ts` at depth `d` over `S`. -/
theorem realize_locDeForm (d : ℕ) (S : Finset J) {n : ℕ}
    (φ : Λ.BoundedFormulaω Empty n)
    (ts : Fin n → Λ[[J]].Term Empty) (hsub : ∀ i, locJSupport Λ J (ts i) ⊆ S) :
    (locDeForm Λ J S φ ts hsub).Realize Empty.elim (fun i : Fin S.card => a (d + i)) ↔
      φ.Realize Empty.elim (fun i => locDeepInterp Λ J a d S (ts i)) := by
  have hassign : (fun i => (locDeTermFin Λ J S (ts i) (hsub i)).realize
        (fun i : Fin S.card => a (d + i)))
      = (fun i => locDeepInterp Λ J a d S (ts i)) :=
    funext fun i => (locDeTermFin_realize Λ J a d S (ts i) (hsub i)).symm
  rw [locDeForm, canonDeForm, BoundedFormulaω.realize_relabel_sumInr_zero]
  simp only [Formulaω.realize_def, BoundedFormulaω.realize_subst]
  rw [hassign]
  exact realize_openBounds φ _

/-- Deep interpretation commutes with `Fin.snoc`: interpreting the one-point extension
`Fin.snoc ts u` gives the snoc of the interpretations. Semantic prep for the later truth lemma's
`all` case (relating the carrier's `∀x` over term-classes to the body's argument tuple). -/
theorem locDeepInterp_snoc (d : ℕ) (S : Finset J) {n : ℕ}
    (ts : Fin n → Λ[[J]].Term Empty) (u : Λ[[J]].Term Empty) :
    (fun i => locDeepInterp Λ J a d S
        ((Fin.snoc ts u : Fin (n + 1) → Λ[[J]].Term Empty) i))
      = Fin.snoc (fun i => locDeepInterp Λ J a d S (ts i)) (locDeepInterp Λ J a d S u) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

/-! ### Eventual deep equality `LocalEMEq` and the support-enlargement engine -/

/-- **Eventual deep equality**: closed terms `t, u` are identified when, for all sufficiently deep
interpretations of their **combined** skeleton support, they evaluate equally in `M`. (The combined
support means both terms are read against the same ordered finite skeleton.) -/
def LocalEMEq (t u : Λ[[J]].Term Empty) : Prop :=
  ∀ᶠ d in Filter.atTop,
    locDeepInterp Λ J a d (locJSupport Λ J t ∪ locJSupport Λ J u) t =
      locDeepInterp Λ J a d (locJSupport Λ J t ∪ locJSupport Λ J u) u

theorem LocalEMEq.refl (t : Λ[[J]].Term Empty) : LocalEMEq Λ J a t t :=
  Filter.Eventually.of_forall fun _ => rfl

theorem LocalEMEq.symm {t u : Λ[[J]].Term Empty} (h : LocalEMEq Λ J a t u) :
    LocalEMEq Λ J a u t := by
  unfold LocalEMEq
  rw [Finset.union_comm (locJSupport Λ J u) (locJSupport Λ J t)]
  exact h.mono fun _ hd => hd.symm

/-- **Support-enlargement invariance** (the atom-slice payoff): if `t, u` are eventually deep-equal
on their combined support `S₀` (i.e. `LocalEMEq t u`) and the de-substituted equality atom of `S₀`
lies in a tail-indiscernible family `Γ`, then they are eventually deep-equal on *any* larger support
`S ⊇ S₀`. Tail indiscernibility identifies the truth of the one arity-`S₀.card` atom on the
consecutive `S₀`-tuple and on the strictly-increasing `S`-tuple; the two atom bridges convert those
to the `S₀`- and `S`-deep equalities. The unlock for `LocalEMContext.trans` and congruence. -/
private theorem LocalEMEq_eventually_on_superset
    {Γ : Set (Σ n, Λ.BoundedFormulaω Empty n)}
    (hind : IsLomega1omegaIndiscernibleOnTail (L := Λ) a Γ)
    {t u : Λ[[J]].Term Empty}
    (hmem : (⟨(locJSupport Λ J t ∪ locJSupport Λ J u).card,
        locDeEqAtom Λ J (locJSupport Λ J t ∪ locJSupport Λ J u) t u Finset.subset_union_left
          Finset.subset_union_right⟩ : Σ n, Λ.BoundedFormulaω Empty n) ∈ Γ)
    (h : LocalEMEq Λ J a t u) {S : Finset J} (hS : locJSupport Λ J t ∪ locJSupport Λ J u ⊆ S) :
    ∀ᶠ d in Filter.atTop, locDeepInterp Λ J a d S t = locDeepInterp Λ J a d S u := by
  set S₀ := locJSupport Λ J t ∪ locJSupport Λ J u with hS₀def
  obtain ⟨N, hN⟩ := hind hmem
  rw [LocalEMEq, Filter.eventually_atTop] at h
  obtain ⟨N₀, hN₀⟩ := h
  rw [Filter.eventually_atTop]
  refine ⟨max N N₀, fun d hd => ?_⟩
  have hdN : N ≤ d := le_trans (le_max_left _ _) hd
  have hdN₀ : N₀ ≤ d := le_trans (le_max_right _ _) hd
  have hsmono : StrictMono (fun i : Fin S₀.card => d + (i : ℕ)) :=
    fun i i' hii' => Nat.add_lt_add_left hii' d
  have hs'mono : StrictMono (fun i : Fin S₀.card => d + deepRank J S (S₀.orderEmbOfFin rfl i)) := by
    intro i i' hii'
    refine Nat.add_lt_add_left
      (deepRank_lt_of_lt (J := J) ?_ ((S₀.orderEmbOfFin rfl).strictMono hii')) d
    exact hS (Finset.orderEmbOfFin_mem S₀ rfl i)
  have hiff := hN (fun i => d + (i : ℕ)) (fun i => d + deepRank J S (S₀.orderEmbOfFin rfl i))
    hsmono hs'mono (fun k => le_trans hdN (Nat.le_add_right d k))
    (fun k => le_trans hdN (Nat.le_add_right d _))
  have hb0 := realize_locDeEqAtom Λ J a d S₀ t u Finset.subset_union_left Finset.subset_union_right
  have hbS := realize_locDeEqAtom_superset Λ J a d hS t u Finset.subset_union_left
    Finset.subset_union_right
  exact hbS.mp (hiff.mp (hb0.mpr (hN₀ d hdN₀)))

/-- **Support-enlargement *iff*** (the symmetric core): on the deep tail the deep equality over the
combined support `S₀` is *equivalent* to the deep equality over any larger support `S ⊇ S₀`. Both
directions — descending from a larger support back to `S₀` is what `LocalEMContext.trans` needs. -/
theorem eventually_locDeepInterp_superset_iff
    {Γ : Set (Σ n, Λ.BoundedFormulaω Empty n)}
    (hind : IsLomega1omegaIndiscernibleOnTail (L := Λ) a Γ)
    {t u : Λ[[J]].Term Empty}
    (hmem : (⟨(locJSupport Λ J t ∪ locJSupport Λ J u).card,
        locDeEqAtom Λ J (locJSupport Λ J t ∪ locJSupport Λ J u) t u Finset.subset_union_left
          Finset.subset_union_right⟩ : Σ n, Λ.BoundedFormulaω Empty n) ∈ Γ)
    {S : Finset J} (hS : locJSupport Λ J t ∪ locJSupport Λ J u ⊆ S) :
    ∀ᶠ d in Filter.atTop,
      (locDeepInterp Λ J a d (locJSupport Λ J t ∪ locJSupport Λ J u) t
            = locDeepInterp Λ J a d (locJSupport Λ J t ∪ locJSupport Λ J u) u ↔
          locDeepInterp Λ J a d S t = locDeepInterp Λ J a d S u) := by
  obtain ⟨N, hN⟩ := hind hmem
  rw [Filter.eventually_atTop]
  refine ⟨N, fun d hd => ?_⟩
  set S₀ := locJSupport Λ J t ∪ locJSupport Λ J u with hS₀def
  have hsmono : StrictMono (fun i : Fin S₀.card => d + (i : ℕ)) :=
    fun i i' hii' => Nat.add_lt_add_left hii' d
  have hs'mono : StrictMono (fun i : Fin S₀.card => d + deepRank J S (S₀.orderEmbOfFin rfl i)) := by
    intro i i' hii'
    refine Nat.add_lt_add_left
      (deepRank_lt_of_lt (J := J) ?_ ((S₀.orderEmbOfFin rfl).strictMono hii')) d
    exact hS (Finset.orderEmbOfFin_mem S₀ rfl i)
  have hiff := hN (fun i => d + (i : ℕ)) (fun i => d + deepRank J S (S₀.orderEmbOfFin rfl i))
    hsmono hs'mono (fun k => le_trans hd (Nat.le_add_right d k))
    (fun k => le_trans hd (Nat.le_add_right d _))
  have hb0 := realize_locDeEqAtom Λ J a d S₀ t u Finset.subset_union_left Finset.subset_union_right
  have hbS := realize_locDeEqAtom_superset Λ J a d hS t u Finset.subset_union_left
    Finset.subset_union_right
  exact Iff.trans hb0.symm (Iff.trans hiff hbS)

/-- **Relation support-independence** (the relation analogue of the previous *iff*): on the deep
tail, the truth of `R` on the deep interpretations over the combined support `S₀` of the
arguments is
equivalent to its truth over any larger support `S ⊇ S₀`. Makes the quotient `RelMap` independent of
the chosen common support. -/
private theorem eventually_locRelMap_superset_iff
    {Γ : Set (Σ n, Λ.BoundedFormulaω Empty n)}
    (hind : IsLomega1omegaIndiscernibleOnTail (L := Λ) a Γ)
    {l : ℕ} (R : Λ.Relations l) {ts : Fin l → Λ[[J]].Term Empty}
    (hmem : (⟨(Finset.univ.biUnion fun i => locJSupport Λ J (ts i)).card,
        locDeRelAtom Λ J (Finset.univ.biUnion fun i => locJSupport Λ J (ts i)) R ts
          fun i => Finset.subset_biUnion_of_mem (fun i => locJSupport Λ J (ts i))
            (Finset.mem_univ i)⟩ : Σ n, Λ.BoundedFormulaω Empty n) ∈ Γ)
    {S : Finset J} (hS : (Finset.univ.biUnion fun i => locJSupport Λ J (ts i)) ⊆ S) :
    ∀ᶠ d in Filter.atTop,
      (Structure.RelMap R
            (fun i => locDeepInterp Λ J a d
              (Finset.univ.biUnion fun i => locJSupport Λ J (ts i)) (ts i)) ↔
        Structure.RelMap R (fun i => locDeepInterp Λ J a d S (ts i))) := by
  obtain ⟨N, hN⟩ := hind hmem
  rw [Filter.eventually_atTop]
  refine ⟨N, fun d hd => ?_⟩
  set S₀ := Finset.univ.biUnion fun i => locJSupport Λ J (ts i) with hS₀def
  have hsmono : StrictMono (fun i : Fin S₀.card => d + (i : ℕ)) :=
    fun i i' hii' => Nat.add_lt_add_left hii' d
  have hs'mono : StrictMono (fun i : Fin S₀.card => d + deepRank J S (S₀.orderEmbOfFin rfl i)) := by
    intro i i' hii'
    refine Nat.add_lt_add_left
      (deepRank_lt_of_lt (J := J) ?_ ((S₀.orderEmbOfFin rfl).strictMono hii')) d
    exact hS (Finset.orderEmbOfFin_mem S₀ rfl i)
  have hiff := hN (fun i => d + (i : ℕ)) (fun i => d + deepRank J S (S₀.orderEmbOfFin rfl i))
    hsmono hs'mono (fun k => le_trans hd (Nat.le_add_right d k))
    (fun k => le_trans hd (Nat.le_add_right d _))
  have hb0 := realize_locDeRelAtom Λ J a d S₀ R ts
    fun i => Finset.subset_biUnion_of_mem (fun i => locJSupport Λ J (ts i)) (Finset.mem_univ i)
  have hbS := realize_locDeRelAtom_superset Λ J a d hS R ts
    fun i => Finset.subset_biUnion_of_mem (fun i => locJSupport Λ J (ts i)) (Finset.mem_univ i)
  exact Iff.trans hb0.symm (Iff.trans hiff hbS)

end DeepInterp

/-! ### The local EM quotient context

To avoid threading the indiscernible sequence, its tail-indiscernible family, and the atomic-diagram
membership through every congruence proof, we bundle them in a `LocalEMContext`. Every quotient
operation then uses `LocalEMEq_eventually_on_superset` (via the support-enlargement *iff*) as its
standing congruence engine. Generic over `Λ` and `[Λ.Structure M]`; the countable local instance is
built in `LocalEMExtraction.lean`. -/

section Quotient

variable {M : Type} [Λ.Structure M]

/-- The **standing data** for the local EM quotient over a fixed source model `M`: a sequence `a` of
deep indiscernibles, a tail-indiscernible family `Γ`, and the fact that every de-substituted atom
lies in `Γ`. The structure accepts an *arbitrary* `Γ`; the countable local family `ΓEMlocal` and its
tail-indiscernible sequence discharge these fields at instantiation (`LocalEMExtraction.lean`). -/
structure LocalEMContext where
  /-- The deep indiscernible sequence. -/
  a : ℕ → M
  /-- The tail-indiscernible formula family. -/
  Γ : Set (Σ n, Λ.BoundedFormulaω Empty n)
  /-- Tail indiscernibility of `a` on `Γ`. -/
  hind : IsLomega1omegaIndiscernibleOnTail (L := Λ) a Γ
  /-- Every de-substituted equality atom is in `Γ`. -/
  atom_mem : ∀ (S : Finset J) (t u : Λ[[J]].Term Empty)
    (ht : locJSupport Λ J t ⊆ S) (hu : locJSupport Λ J u ⊆ S),
    (⟨S.card, locDeEqAtom Λ J S t u ht hu⟩ : Σ n, Λ.BoundedFormulaω Empty n) ∈ Γ
  /-- Every de-substituted relation atom is in `Γ`. -/
  rel_mem : ∀ (S : Finset J) {l : ℕ} (R : Λ.Relations l)
    (ts : Fin l → Λ[[J]].Term Empty) (ht : ∀ i, locJSupport Λ J (ts i) ⊆ S),
    (⟨S.card, locDeRelAtom Λ J S R ts ht⟩ : Σ n, Λ.BoundedFormulaω Empty n) ∈ Γ

/-- Support monotonicity: an argument's skeleton support is contained in the whole term's. -/
theorem locJSupport_subterm {α : Type} {n : ℕ} (f : Λ[[J]].Functions n)
    (ts : Fin n → Λ[[J]].Term α) (i : Fin n) :
    locJSupport Λ J (ts i) ⊆ locJSupport Λ J (.func f ts) := fun _ hx =>
  Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)

/-- **Transitivity of `LocalEMEq`** (the congruence engine's first payoff): enlarge to the union of
all three supports, transport both hypotheses up to it via the enlargement *iff*, chain the
equalities in `M`, and descend back to the `(t,v)`-support. -/
theorem LocalEMContext.trans (ctx : LocalEMContext Λ J (M := M))
    {t u v : Λ[[J]].Term Empty}
    (h1 : LocalEMEq Λ J ctx.a t u) (h2 : LocalEMEq Λ J ctx.a u v) : LocalEMEq Λ J ctx.a t v := by
  set S := locJSupport Λ J t ∪ locJSupport Λ J u ∪ locJSupport Λ J v with hSdef
  have hsub_tu : locJSupport Λ J t ∪ locJSupport Λ J u ⊆ S := Finset.subset_union_left
  have hsub_uv : locJSupport Λ J u ∪ locJSupport Λ J v ⊆ S :=
    Finset.union_subset
      ((Finset.subset_union_right).trans Finset.subset_union_left) Finset.subset_union_right
  have hsub_tv : locJSupport Λ J t ∪ locJSupport Λ J v ⊆ S :=
    Finset.union_subset
      ((Finset.subset_union_left).trans Finset.subset_union_left) Finset.subset_union_right
  have iff_tu := eventually_locDeepInterp_superset_iff Λ J ctx.a ctx.hind
    (ctx.atom_mem _ t u Finset.subset_union_left Finset.subset_union_right) hsub_tu
  have iff_uv := eventually_locDeepInterp_superset_iff Λ J ctx.a ctx.hind
    (ctx.atom_mem _ u v Finset.subset_union_left Finset.subset_union_right) hsub_uv
  have iff_tv := eventually_locDeepInterp_superset_iff Λ J ctx.a ctx.hind
    (ctx.atom_mem _ t v Finset.subset_union_left Finset.subset_union_right) hsub_tv
  have hS_tu := (h1.and iff_tu).mono (fun _ p => p.2.mp p.1)
  have hS_uv := (h2.and iff_uv).mono (fun _ p => p.2.mp p.1)
  have hS_tv := (hS_tu.and hS_uv).mono (fun _ p => p.1.trans p.2)
  exact (iff_tv.and hS_tv).mono (fun _ p => p.1.mpr p.2)

/-- **Function congruence**: if the arguments are pairwise `LocalEMEq`, so are the function terms.
Enlarge every argument's deep equality up to the whole term's support, combine the finitely many
eventual equalities, and apply `locDeepInterp_func`. -/
theorem LocalEMContext.func_congr (ctx : LocalEMContext Λ J (M := M)) {n : ℕ}
    (f : Λ[[J]].Functions n) {ts ts' : Fin n → Λ[[J]].Term Empty}
    (h : ∀ i, LocalEMEq Λ J ctx.a (ts i) (ts' i)) :
    LocalEMEq Λ J ctx.a (.func f ts) (.func f ts') := by
  unfold LocalEMEq
  set S₀ := locJSupport Λ J (.func f ts) ∪ locJSupport Λ J (.func f ts') with hS₀
  have hi : ∀ i, ∀ᶠ d in Filter.atTop,
      locDeepInterp Λ J ctx.a d S₀ (ts i) = locDeepInterp Λ J ctx.a d S₀ (ts' i) := by
    intro i
    refine LocalEMEq_eventually_on_superset Λ J ctx.a ctx.hind
      (ctx.atom_mem _ (ts i) (ts' i) Finset.subset_union_left Finset.subset_union_right) (h i) ?_
    exact Finset.union_subset
      ((locJSupport_subterm Λ J f ts i).trans Finset.subset_union_left)
      ((locJSupport_subterm Λ J f ts' i).trans Finset.subset_union_right)
  refine (Filter.eventually_all.mpr hi).mono (fun d hd => ?_)
  rw [locDeepInterp_func, locDeepInterp_func]
  congr 1
  funext i
  exact hd i

/-- `LocalEMEq` is an equivalence relation on closed terms (refl/symm need no context; trans is
`LocalEMContext.trans`). -/
def LocalEMContext.setoid (ctx : LocalEMContext Λ J (M := M)) :
    Setoid (Λ[[J]].Term Empty) where
  r := LocalEMEq Λ J ctx.a
  iseqv := ⟨fun t => LocalEMEq.refl Λ J ctx.a t, fun h => LocalEMEq.symm Λ J ctx.a h,
    fun h1 h2 => LocalEMContext.trans (Λ := Λ) (J := J) ctx h1 h2⟩

/-- The **local EM term-model carrier** for a context: closed `Λ[[J]]`-terms modulo `LocalEMEq`. -/
def LocalEMContext.Carrier (ctx : LocalEMContext Λ J (M := M)) : Type :=
  Quotient ctx.setoid

/-- A closed term as an element of the carrier. -/
def LocalEMContext.mkClass (ctx : LocalEMContext Λ J (M := M)) (t : Λ[[J]].Term Empty) :
    ctx.Carrier :=
  Quotient.mk ctx.setoid t

/-- A common support covering all argument representatives — the support over which a
relation's deep
truth is read. -/
private noncomputable def LocalEMContext.commonSupport (ctx : LocalEMContext Λ J (M := M)) {n : ℕ}
    (xs : Fin n → ctx.Carrier) : Finset J :=
  Finset.univ.biUnion fun i => locJSupport Λ J (Quotient.out (xs i))

/-- The **local EM term-model structure** on the carrier: function symbols act by term formation
`f([ts]) := [func f ts]` (skeleton constants are the arity-0 case), and a relation holds iff
it holds
in `M` on the deep interpretations for all sufficiently deep `d` (read over a common support of the
arguments). Well-definedness is proved separately via the enlargement-invariance congruence
  engine. -/
@[reducible] noncomputable def LocalEMContext.structure (ctx : LocalEMContext Λ J (M := M)) :
    Λ[[J]].Structure ctx.Carrier where
  funMap {_} f xs := Quotient.mk ctx.setoid (Term.func f fun i => Quotient.out (xs i))
  RelMap {n} R xs :=
    ∀ᶠ d in Filter.atTop,
      letI : (constantsOn J).Structure M :=
        constantsOn.structure fun j => ctx.a (d + deepRank J (ctx.commonSupport (xs := xs)) j)
      @Structure.RelMap (Λ[[J]]) M _ n R
        fun i => locDeepInterp Λ J ctx.a d (ctx.commonSupport (xs := xs)) (Quotient.out (xs i))

/-- **Function interpretation computes on classes** (well-definedness): applying the interpreted
function symbol to a tuple of term-classes gives the class of the function term. Immediate from
`func_congr` and `Quotient.out_eq`. (The arity-0 case is `constMap_mkClass`.) -/
theorem LocalEMContext.funMap_mkClass (ctx : LocalEMContext Λ J (M := M)) {n : ℕ}
    (f : Λ[[J]].Functions n) (ts : Fin n → Λ[[J]].Term Empty) :
    @Structure.funMap (Λ[[J]]) ctx.Carrier ctx.structure n f
        (fun i => ctx.mkClass (t := ts i)) = ctx.mkClass (t := .func f ts) := by
  apply Quotient.sound
  apply ctx.func_congr
  exact fun i => Quotient.exact (Quotient.out_eq (ctx.mkClass (t := ts i)))

/-- The arity-0 case: a skeleton constant `c_j` (or any `Λ`-constant) interprets as the class of its
constant term. -/
theorem LocalEMContext.constMap_mkClass (ctx : LocalEMContext Λ J (M := M))
    (c : Λ[[J]].Functions 0) :
    @Structure.funMap (Λ[[J]]) ctx.Carrier ctx.structure 0 c Fin.elim0
      = ctx.mkClass (t := .func c Fin.elim0) := by
  apply Quotient.sound
  apply ctx.func_congr
  exact fun i => i.elim0

/-- **Relation congruence on terms** (helper): changing a finite tuple of argument terms by
`LocalEMEq`, all over a fixed covering support `T`, preserves the eventual deep truth of a relation.
Combines the per-term equality invariance over `T` with `Filter.eventually_all`. -/
private theorem LocalEMContext.eventually_relMap_congr_terms (ctx : LocalEMContext Λ J (M :=
  M)) {l : ℕ}
    (R : Λ.Relations l) {ts ts' : Fin l → Λ[[J]].Term Empty}
    (h : ∀ i, LocalEMEq Λ J ctx.a (ts i) (ts' i)) {T : Finset J}
    (hts : ∀ i, locJSupport Λ J (ts i) ⊆ T) (hts' : ∀ i, locJSupport Λ J (ts' i) ⊆ T) :
    (∀ᶠ d in Filter.atTop, Structure.RelMap R fun i => locDeepInterp Λ J ctx.a d T (ts i)) ↔
      (∀ᶠ d in Filter.atTop, Structure.RelMap R fun i => locDeepInterp Λ J ctx.a d T (ts' i)) := by
  have hcong : ∀ᶠ d in Filter.atTop, ∀ i,
      locDeepInterp Λ J ctx.a d T (ts i) = locDeepInterp Λ J ctx.a d T (ts' i) :=
    Filter.eventually_all.mpr fun i =>
      LocalEMEq_eventually_on_superset Λ J ctx.a ctx.hind
        (ctx.atom_mem _ (ts i) (ts' i) Finset.subset_union_left Finset.subset_union_right) (h i)
        (Finset.union_subset (hts i) (hts' i))
  exact Filter.eventually_congr (hcong.mono fun _ hd => Iff.of_eq (congrArg _ (funext hd)))

/-- **Relation interpretation computes on classes** (well-definedness): the interpreted relation
holds on a tuple of term-classes iff it holds in `M` on the deep interpretations for all
sufficiently
deep `d`, over *any* support `S` covering the arguments — independent of the representatives and of
the chosen support. The relation analogue of `funMap_mkClass`, via a bridge support `T = S ∪
  Sout`. -/
theorem LocalEMContext.relMap_mkClass_iff (ctx : LocalEMContext Λ J (M := M)) {l : ℕ}
    (R : Λ.Relations l) (ts : Fin l → Λ[[J]].Term Empty)
    {S : Finset J} (hS : (Finset.univ.biUnion fun i => locJSupport Λ J (ts i)) ⊆ S) :
    @Structure.RelMap (Λ[[J]]) ctx.Carrier ctx.structure l (Sum.inl R)
        (fun i => ctx.mkClass (t := ts i)) ↔
      ∀ᶠ d in Filter.atTop, Structure.RelMap R fun i => locDeepInterp Λ J ctx.a d S (ts i) := by
  change (∀ᶠ d in Filter.atTop, Structure.RelMap R fun i =>
        locDeepInterp Λ J ctx.a d
          (Finset.univ.biUnion fun i => locJSupport Λ J (Quotient.out (ctx.mkClass (t := ts i))))
          (Quotient.out (ctx.mkClass (t := ts i)))) ↔ _
  set rep : Fin l → Λ[[J]].Term Empty :=
    fun i => Quotient.out (ctx.mkClass (t := ts i)) with hrep
  set Sout : Finset J := Finset.univ.biUnion fun i => locJSupport Λ J (rep i) with hSout
  set T : Finset J := S ∪ Sout with hT
  have hrep_eq : ∀ i, LocalEMEq Λ J ctx.a (rep i) (ts i) :=
    fun i => Quotient.exact (Quotient.out_eq (ctx.mkClass (t := ts i)))
  have hSout_T : Sout ⊆ T := Finset.subset_union_right
  have hS_T : S ⊆ T := Finset.subset_union_left
  have hrep_T : ∀ i, locJSupport Λ J (rep i) ⊆ T := fun i =>
    (Finset.subset_biUnion_of_mem (fun i => locJSupport Λ J (rep i)) (Finset.mem_univ i)).trans
      hSout_T
  have hts_S : ∀ i, locJSupport Λ J (ts i) ⊆ S := fun i =>
    (Finset.subset_biUnion_of_mem (fun i => locJSupport Λ J (ts i)) (Finset.mem_univ i)).trans hS
  have hts_T : ∀ i, locJSupport Λ J (ts i) ⊆ T := fun i => (hts_S i).trans hS_T
  -- (a) move the rep-side from Sout up to T
  have ha := Filter.eventually_congr
    (eventually_locRelMap_superset_iff Λ J ctx.a ctx.hind R (ts := rep)
      (ctx.rel_mem _ R rep fun i =>
        Finset.subset_biUnion_of_mem (fun i => locJSupport Λ J (rep i)) (Finset.mem_univ i))
          hSout_T)
  -- (b) swap reps for ts over T
  have hb := LocalEMContext.eventually_relMap_congr_terms (Λ := Λ) (J := J) ctx R hrep_eq
    hrep_T hts_T
  -- (c) relate the ts-side over T and over S
  have hcT := Filter.eventually_congr
    (eventually_locRelMap_superset_iff Λ J ctx.a ctx.hind R (ts := ts)
      (ctx.rel_mem _ R ts fun i =>
        Finset.subset_biUnion_of_mem (fun i => locJSupport Λ J (ts i)) (Finset.mem_univ i))
      (hS.trans hS_T))
  have hcS := Filter.eventually_congr
    (eventually_locRelMap_superset_iff Λ J ctx.a ctx.hind R (ts := ts)
      (ctx.rel_mem _ R ts fun i =>
        Finset.subset_biUnion_of_mem (fun i => locJSupport Λ J (ts i)) (Finset.mem_univ i)) hS)
  exact ha.trans (hb.trans (hcT.symm.trans hcS))

/-- The **base `Λ`-structure** on the carrier: the reduct of the term-model `[[J]]`-structure along
the skeleton-constant inclusion (a base function/relation symbol acts as its `Sum.inl` image). -/
@[reducible] noncomputable def LocalEMContext.structureBase (ctx : LocalEMContext Λ J (M := M)) :
    Λ.Structure ctx.Carrier where
  funMap {n} f xs := @Structure.funMap (Λ[[J]]) ctx.Carrier ctx.structure n (Sum.inl f) xs
  RelMap {n} R xs := @Structure.RelMap (Λ[[J]]) ctx.Carrier ctx.structure n (Sum.inl R) xs

/-- **Map-language plumbing**: the skeleton-constant inclusion `Λ → Λ[[J]]` is an expansion of the
carrier's base structure to its term-model `[[J]]`-structure (definitional, as the `[[J]]`-structure
interprets `Sum.inl` symbols by the base reduct). Lets `realize_mapLanguage` transfer
realizations of
base-language formulas. -/
theorem LocalEMContext.lhomWithConstants_isExpansionOn (ctx : LocalEMContext Λ J (M := M)) :
    @LHom.IsExpansionOn Λ (Λ[[J]])
      (lhomWithConstants Λ J) ctx.Carrier ctx.structureBase ctx.structure := by
  let : Λ.Structure ctx.Carrier := ctx.structureBase
  let : (Λ[[J]]).Structure ctx.Carrier := ctx.structure
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end Quotient

end FirstOrder.Language
