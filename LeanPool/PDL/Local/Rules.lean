/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/


module

public import LeanPool.PDL.Sequent
public import LeanPool.PDL.Local.UnfoldBox
public import LeanPool.PDL.Local.UnfoldDia
public import Mathlib.Data.Finset.Sort

/-! ## Local rules and local rule applications  -/

public section

namespace PDL

open HasLength

/-! ## One-sided local rules -/

/-- Local rules replace a given set of formulas by other sets, one for each branch.
The set of resulting branches can be empty, representing that the given set is closed.
In the Haskell prover this is done in "ruleFor" in the Logic.PDL.Prove.Tree module. -/
inductive OneSidedLocalRule : Finset Formula → Finset (Finset Formula) → Type
  -- PROP LOGIC
  -- closing rules:
  | bot                 : OneSidedLocalRule {⊥}      ∅
  | not (φ   : Formula) : OneSidedLocalRule {φ, ~φ}  ∅
  | neg (φ   : Formula) : OneSidedLocalRule {~~φ}    {{φ}}
  | con (φ ψ : Formula) : OneSidedLocalRule {φ ⋀ ψ}  {{φ,ψ}}
  | nCo (φ ψ : Formula) : OneSidedLocalRule {~(φ⋀ψ)} {{~φ}, {~ψ}}
  -- PROGRAMS
  -- the two general local rules:
  | box (α φ) : (notAtom : ¬ α.isAtomic) → OneSidedLocalRule { ⌈α⌉φ} (unfoldBox     α φ).pdlToFinFin
  | dia (α φ) : (notAtom : ¬ α.isAtomic) → OneSidedLocalRule {~⌈α⌉φ} (unfoldDiamond α φ).pdlToFinFin
  deriving Repr

/-- The precondition of a `OneSidedLocalRule` determines the rule. -/
theorem OneSidedLocalRule.heq_of_precond_eq : ∀ {X B X' B' : _}
    (a : OneSidedLocalRule X B) (b : OneSidedLocalRule X' B'), X = X' → HEq a b := by
  intro X B X' B' a b h
  cases a <;> cases b <;>
    first
      | rfl
      | exact absurd h (pair_neg_ne_singleton _ _)
      | exact absurd h.symm (pair_neg_ne_singleton _ _)
      | (cases pair_neg_inj h; rfl)
      | (exfalso; simp_all; done)
      | (rw [Finset.singleton_inj] at h; injections; subst_eqs; rfl)

instance oneSidedLocalRuleSubsingleton (X B) : Subsingleton (OneSidedLocalRule X B) :=
  ⟨fun a b => eq_of_heq (OneSidedLocalRule.heq_of_precond_eq a b rfl)⟩

instance : DecidableEq (OneSidedLocalRule X B) := fun a b => isTrue (Subsingleton.elim a b)

theorem oneSidedLocalRuleTruth (lr : OneSidedLocalRule X B) :
      con X.sort ≡ B.pdlDiscon :=
  by
  intro W M w
  cases lr
  all_goals
    try
      simp only [Finset.sort_singleton, con.eq_2, evaluate, Finset.disconEval,
        Finset.notMem_empty, false_and, exists_const, evaluate_con_sort, Finset.mem_insert,
        Finset.mem_singleton, forall_eq_or_imp, forall_eq, and_not_self, evaluate.eq_3, not_not,
        exists_eq_left, evaluate.eq_4, not_and, exists_eq_or_imp, ↓existsAndEq, true_and]
      try tauto
      done
    -- takes care of all propositional rules
  case box α φ notAtom =>
    rw [conEval]
    simp only [Finset.sort_singleton, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      evaluate, List.pdlToFinFin]
    have := localBoxTruth α φ W M w
    simp only [evaluate, disEval, List.mem_map, exists_exists_and_eq_and, unfoldBox, List.map_map,
      Finset.disconEval, List.mem_toFinset, Function.comp_apply] at *
    convert this
    rw [conEval]
  case dia α φ notAtom =>
    rw [conEval, Finset.disconEval]
    simp only [Finset.sort_singleton, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.pdlToFinFin, List.mem_toFinset, List.mem_map, exists_exists_and_eq_and]
    have := localDiamondTruth α φ W M w
    rw [disEval] at this
    simp only [List.mem_map, Prod.exists, ↓existsAndEq, and_true] at this
    unfold unfoldDiamond
    simp only [List.mem_map, Prod.exists, ↓existsAndEq, and_true]
    convert this
    rw [conEval]

/-- All one-sided local rules have a non-empty precondition. -/
lemma OneSidedLocalRule.precond_ne_nil {precond ress} (orule : OneSidedLocalRule precond ress) :
    precond ≠ {} := by
  cases orule <;> simp

/-! ## Loaded Rules -/

/-- Convert list-valued formula components to finsets while preserving optional loadings. -/
@[simp]
def _root_.List.pdlToFinFinOpt [DecidableEq α] [DecidableEq β] :
    List (List α × Option β) → Finset (Finset α × Option β)
  | LS => (LS.map (fun ⟨L,O⟩ => ⟨L.toFinset, O⟩)).toFinset

/-- The loaded diamond rule, given by `unfoldDiamondLoaded`.
In MB page 19 these were multiple rules ¬u, ¬; ¬* and ¬?.
It replaces the loaded formula by up to one loaded formula and a list of normal formulas.
It's a bit annoying to need the rule twice here due to the definition of LoadFormula
and the extra definition of `unfoldDiamondLoaded'`. -/
inductive LoadRule : NegLoadFormula → Finset (Finset Formula × Option NegLoadFormula) → Type
  | dia  {α χ} : (notAtom : ¬ α.isAtomic)
                → LoadRule (~'⌊α⌋(χ : LoadFormula)) (unfoldDiamondLoaded  α χ).pdlToFinFinOpt
  | dia' {α φ} : (notAtom : ¬ α.isAtomic)
                → LoadRule (~'⌊α⌋(φ : Formula    )) (unfoldDiamondLoaded' α φ).pdlToFinFinOpt
  deriving DecidableEq, Repr

/-- Unloading a pair and then going to `Finset`s is the same as `pairUnloadSet`. -/
lemma toFinset_pairUnload (p : List Formula × Option NegLoadFormula) :
    (pairUnload p).toFinset = pairUnloadSet (p.1.toFinset, p.2) := by
  rcases p with ⟨L, _ | nlf⟩ <;> simp [pairUnload, pairUnloadSet]

lemma unfoldDiamondLoaded_eqFin α χ :
    (unfoldDiamond α χ.unload).pdlToFinFin
    = (Finset.image pairUnloadSet (unfoldDiamondLoaded α χ).pdlToFinFinOpt) := by
  rw [← unfoldDiamondLoaded_eq α χ]
  simp only [List.pdlToFinFin, List.pdlToFinFinOpt, List.toFinset_map_eq_image, List.map_map,
    Finset.image_image]
  congr 1
  funext p
  exact toFinset_pairUnload p

lemma unfoldDiamondLoaded'_eqFin α φ :
    (unfoldDiamond α φ).pdlToFinFin
    = (Finset.image pairUnloadSet (unfoldDiamondLoaded' α φ).pdlToFinFinOpt) := by
  rw [← unfoldDiamondLoaded'_eq α φ]
  simp only [List.pdlToFinFin, List.pdlToFinFinOpt, List.toFinset_map_eq_image, List.map_map,
    Finset.image_image]
  congr 1
  funext p
  exact toFinset_pairUnload p

/-- Given a LoadRule application, define the equivalent unloaded rule application.
This allows re-using `oneSidedLocalRuleTruth` to prove `loadRuleTruth`. -/
def LoadRule.unload : LoadRule (~'χ) B → OneSidedLocalRule {~χ.unload} (B.image pairUnloadSet)
| @dia α χ notAtom => unfoldDiamondLoaded_eqFin α χ ▸ OneSidedLocalRule.dia α χ.unload notAtom
| @dia' α φ notAtom => unfoldDiamondLoaded'_eqFin α φ ▸ OneSidedLocalRule.dia α φ notAtom

/-- The loaded unfold rule is sound and invertible.
In the notes this is part of localRuleTruth. -/
theorem loadRuleTruth (lr : LoadRule (~'χ) B) :
    (~χ.unload) ≡ dis (B.image (con ∘ Finset.sort ∘ pairUnloadSet)).sort :=
  by
  intro W M w
  have := oneSidedLocalRuleTruth (lr.unload) W M w
  simp only [Finset.sort_singleton, con.eq_2, evaluate, Finset.disconEval, Finset.mem_image,
    Prod.exists, ↓existsAndEq, and_true] at this
  simp only [evaluate, disEval]
  rw [this]
  clear this
  simp only [Finset.mem_sort, Finset.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨a, b, hab, h⟩
    exact ⟨_, ⟨(a, b), hab, rfl⟩, (evaluate_con_sort _).2 h⟩
  · rintro ⟨f, ⟨p, hp, rfl⟩, hf⟩
    exact ⟨p.1, p.2, hp, (evaluate_con_sort _).1 hf⟩
  /- Old proof, before the refactoring to `Finset`:
  simp only [Prod.exists]
  constructor
  · rintro ⟨Y, ⟨a, ⟨b, ab_in_B, def_Y⟩⟩, w_Y⟩
    use con Y
    simp_all only [conEval, implies_true, and_true]
    use a, b, ab_in_B
    rw [← def_Y]
    simp
  · rintro ⟨f, ⟨a, b, ab_in_B, def_f⟩, w_f⟩
    subst def_f
    simp at w_f
    rw [conEval] at w_f
    use pairUnload (a,b)
    constructor
    · use a, b
    · exact w_f
  -/

/-! ## Local Rules -/

/-- A local rule is a `OneSidedLocalRule`, a left-right contradiction, or a `LoadRule`.
Note that formulas can be in four places: left, right, loaded left, loaded right.

We do *not* have neg/contradiction rules between loaded and unloaded formulas (i.e.
between `({unload χ}, ∅, some (Sum.inl ~χ))` and `(∅, {unload χ}, some (Sum.inr ~χ))`)
because in any such case we could also close the tableau before or without loading.

The `YS_def` arguments in non-terminal rules enables deriving `DecidableEq` for `LocalRule`.
-/
inductive LocalRule : Sequent → Finset Sequent → Type
  | oneSidedL {precond ress YS} (orule : OneSidedLocalRule precond ress)
      (YS_def : YS = ress.image fun res => (res,∅,none)) : LocalRule (precond,∅,none) YS
  | oneSidedR {precond ress YS} (orule : OneSidedLocalRule precond ress)
      (YS_def : YS = ress.image fun res => (∅,res,none)) : LocalRule (∅,precond,none) YS
  | LRnegL (ϕ : Formula) : LocalRule ({ϕ}, {~ϕ}, none) ∅ --  ϕ on left side, ~ϕ on the right
  | LRnegR (ϕ : Formula) : LocalRule ({~ϕ}, {ϕ}, none) ∅ -- ~ϕ on left side,  ϕ on the right
  | loadedL {ress YS} (χ : LoadFormula) (lrule : LoadRule (~'χ) ress)
      (YS_def : YS = ress.image fun (X, o) => (X, ∅, o.map Sum.inl))
      : LocalRule (∅, ∅, some (Sum.inl (~'χ))) YS
  | loadedR {ress YS} (χ : LoadFormula) (lrule : LoadRule (~'χ) ress)
      (YS_def : YS = ress.image fun (X, o) => (∅, X, o.map Sum.inr))
      : LocalRule (∅, ∅, some (Sum.inr (~'χ))) YS
  deriving Repr

/-- The loaded formula determines the `LoadRule`. -/
theorem LoadRule.heq_of_index_eq : ∀ {χ χ' B B'}
    (a : LoadRule χ B) (b : LoadRule χ' B'), χ = χ' → HEq a b := by
  intro χ χ' B B' a b h
  cases a <;> cases b <;> injections <;> subst_eqs <;> rfl

instance loadRuleSubsingleton (χ B) : Subsingleton (LoadRule χ B) :=
  ⟨fun a b => eq_of_heq (LoadRule.heq_of_index_eq a b rfl)⟩

-- many cases to consider
/-- The source and the results determine a `LocalRule`. -/
theorem LocalRule.heq_of_index_eq : ∀ {X X' YS YS'}
    (a : LocalRule X YS) (b : LocalRule X' YS'), X = X' → YS = YS' → HEq a b := by
  intro X X' YS YS' a b hX hYS
  cases a <;> cases b <;>
    (have hL := congrArg Sequent.L hX
     have hR := congrArg Sequent.R hX
     have hO := congrArg Sequent.O hX
     simp only [Sequent.L_eq, Sequent.R_eq, Sequent.O_eq] at hL hR hO
     clear hX)
  case oneSidedL.oneSidedL precond ress orule YS_def precond' ress' orule' YS_def' =>
    subst YS_def; subst YS_def'
    have hress : ress = ress' := by
      refine Finset.image_injective ?_ hYS
      intro A A' hab
      simpa [Sequent.L_eq] using congrArg Sequent.L hab
    subst hress; subst hL
    have : orule = orule' := Subsingleton.elim _ _
    subst this; rfl
  case oneSidedL.oneSidedR precond ress orule YS_def precond' ress' orule' YS_def' =>
    exact absurd hL orule.precond_ne_nil
  case oneSidedL.LRnegL => simp at hR
  case oneSidedL.LRnegR => simp at hR
  case oneSidedL.loadedL => simp at hO
  case oneSidedL.loadedR => simp at hO
  case oneSidedR.oneSidedL precond ress orule YS_def precond' ress' orule' YS_def' =>
    exact absurd hR orule.precond_ne_nil
  case oneSidedR.oneSidedR precond ress orule YS_def precond' ress' orule' YS_def' =>
    subst YS_def; subst YS_def'
    have hress : ress = ress' := by
      refine Finset.image_injective ?_ hYS
      intro A A' hab
      simpa [Sequent.R_eq] using congrArg Sequent.R hab
    subst hress; subst hR
    have : orule = orule' := Subsingleton.elim _ _
    subst this; rfl
  case oneSidedR.LRnegL => simp at hL
  case oneSidedR.LRnegR => simp at hL
  case oneSidedR.loadedL => simp at hO
  case oneSidedR.loadedR => simp at hO
  case LRnegL.oneSidedL => simp at hR
  case LRnegL.oneSidedR => simp at hL
  case LRnegL.LRnegL => rw [Finset.singleton_inj] at hL; subst hL; rfl
  case LRnegL.LRnegR ϕ ϕ' =>
    rw [Finset.singleton_inj] at hL hR
    exact absurd (hL.trans (congrArg Formula.neg hR.symm)) (Formula.ne_neg_neg_self ϕ)
  case LRnegL.loadedL => simp at hO
  case LRnegL.loadedR => simp at hO
  case LRnegR.oneSidedL => simp at hR
  case LRnegR.oneSidedR => simp at hL
  case LRnegR.LRnegL ϕ ϕ' =>
    rw [Finset.singleton_inj] at hL hR
    exact absurd (hR.trans (congrArg Formula.neg hL.symm)) (Formula.ne_neg_neg_self ϕ)
  case LRnegR.LRnegR => rw [Finset.singleton_inj] at hR; subst hR; rfl
  case LRnegR.loadedL => simp at hO
  case LRnegR.loadedR => simp at hO
  case loadedL.oneSidedL => simp at hO
  case loadedL.oneSidedR => simp at hO
  case loadedL.LRnegL => simp at hO
  case loadedL.LRnegR => simp at hO
  case loadedL.loadedL ress χ lrule YS_def ress' χ' lrule' YS_def' =>
    subst YS_def; subst YS_def'
    simp only [Option.some.injEq, Sum.inl.injEq, NegLoadFormula.neg.injEq] at hO
    subst hO
    have hress : ress = ress' := by
      refine Finset.image_injective ?_ hYS
      rintro ⟨A, o⟩ ⟨A', o'⟩ hab
      have h1 := congrArg Sequent.L hab
      have h3 := congrArg Sequent.O hab
      simp only [Sequent.L_eq, Sequent.O_eq] at h1 h3
      cases o <;> cases o' <;> simp_all
    subst hress
    have : lrule = lrule' := Subsingleton.elim _ _
    subst this; rfl
  case loadedL.loadedR => simp at hO
  case loadedR.oneSidedL => simp at hO
  case loadedR.oneSidedR => simp at hO
  case loadedR.LRnegL => simp at hO
  case loadedR.LRnegR => simp at hO
  case loadedR.loadedL => simp at hO
  case loadedR.loadedR ress χ lrule YS_def ress' χ' lrule' YS_def' =>
    subst YS_def; subst YS_def'
    simp only [Option.some.injEq, Sum.inr.injEq, NegLoadFormula.neg.injEq] at hO
    subst hO
    have hress : ress = ress' := by
      refine Finset.image_injective ?_ hYS
      rintro ⟨A, o⟩ ⟨A', o'⟩ hab
      have h1 := congrArg Sequent.R hab
      have h3 := congrArg Sequent.O hab
      simp only [Sequent.R_eq, Sequent.O_eq] at h1 h3
      cases o <;> cases o' <;> simp_all
    subst hress
    have : lrule = lrule' := Subsingleton.elim _ _
    subst this; rfl

instance localRuleSubsingleton (X YS) : Subsingleton (LocalRule X YS) :=
  ⟨fun a b => eq_of_heq (LocalRule.heq_of_index_eq a b rfl rfl)⟩

instance {YS} : DecidableEq (LocalRule X YS) := fun a b => isTrue (Subsingleton.elim a b)

/-- Replace a rule's preconditions by each of its possible result sequents. -/
@[expose, simp] def applyLocalRule {Lcond Rcond Ocond ress} :
  LocalRule (Lcond, Rcond, Ocond) ress → Sequent → Finset Sequent
  | _, ⟨L, R, O⟩ => ress.image <|
      fun (Lnew, Rnew, Onew) => ( L \ Lcond ∪ Lnew
                                , R \ Rcond ∪ Rnew
                                , Olf.change O Ocond Onew )

/-- Helper originally written for Lemma 6.14 but currently unused. -/
def principalFormulaForLocalRule {YS} : LocalRule X YS -> AnyFormula
  | .oneSidedL orule _ =>
      match orule with
        | .bot      => Formula.bottom
        | .con φ ψ =>  (φ ⋀ ψ)
        | .not φ => φ
        | .neg φ => ~~φ
        | .nCo φ ψ => ~(Formula.and φ ψ)
        | .dia α φ _ => ~⌈α⌉φ
        | .box α φ _ => ⌈α⌉φ
  | .oneSidedR orule _ =>
      match orule with
        | .bot      => Formula.bottom
        | .con φ ψ => φ ⋀ ψ
        | .not φ => φ
        | .neg φ => ~~φ
        | .nCo φ ψ => ~(Formula.and φ ψ)
        | .dia α φ _  => ~⌈α⌉φ
        | .box α φ _   => ⌈α⌉φ
  | .LRnegL φ => φ
  | .LRnegR φ => φ
  | .loadedL φ _ _ => φ
  | .loadedR φ _ _ => φ

lemma oneSidedL_preserves_right {LRO : Sequent}
    {Lcond : Finset Formula} (Lpreproof : Lcond ⊆ LRO.L)
    {Lres : Finset (Finset Formula)} (orule : OneSidedLocalRule Lcond Lres)
    {YS : Finset Sequent} (YS_def : YS = Finset.image (fun res => (res, ∅, none)) Lres)
    : ∀ c ∈ applyLocalRule (LocalRule.oneSidedL orule YS_def) LRO, c.right = LRO.right := by
  rcases LRO with ⟨L,R,O⟩
  rintro ⟨L',R',O'⟩
  subst YS_def
  simp at *
  grind

lemma oneSidedR_preserves_left {LRO : Sequent}
    {Rcond : Finset Formula} (Rpreproof : Rcond ⊆ LRO.R)
    {Rres : Finset (Finset Formula)} (orule : OneSidedLocalRule Rcond Rres)
    {YS : Finset Sequent} (YS_def : YS = Finset.image (fun res => (∅, res, none)) Rres)
    : ∀ c ∈ applyLocalRule (LocalRule.oneSidedR orule YS_def) LRO, c.left = LRO.left := by
  rcases LRO with ⟨L,R,O⟩
  rintro ⟨L',R',O'⟩
  subst YS_def
  simp at *
  grind

open HasSat

lemma oneSidedL_sat_down (LRO : Sequent)
    {Lcond : Finset Formula} (Lpreproof : Lcond ⊆ LRO.L)
    {Lres : Finset (Finset Formula)} (orule : OneSidedLocalRule Lcond Lres)
    {YS : Finset Sequent} (YS_def : YS = Finset.image (fun res => (res, ∅, none)) Lres)
    {X : Finset Formula} (LX_sat : satisfiable (Sequent.left LRO ∪ X))
    : ∃ c ∈ applyLocalRule (LocalRule.oneSidedL orule YS_def) LRO, satisfiable (c.left ∪ X) := by
  rcases LRO with ⟨L,R,O⟩
  subst YS_def
  rcases LX_sat with ⟨W, M, w, satM⟩
  have : evaluate M w (con Lcond.sort) := by simp [conEval]; aesop
  have := (oneSidedLocalRuleTruth orule W M w).1 this
  rw [Finset.disconEval] at this
  rcases this with ⟨L', L'_in, w_L'⟩
  simp only [applyLocalRule, Finset.sdiff_empty, Finset.mem_image, exists_exists_and_eq_and,
    Finset.union_empty, Olf.change_old_none_none, Sequent.left_eq, Finset.union_assoc]
  refine ⟨L', L'_in, W, M, w, fun φ φ_in => ?_⟩
  specialize @satM φ
  simp only [Finset.mem_union, Finset.mem_sdiff] at φ_in
  rcases φ_in with φ_in_LnoCond | φ_in_L' | φ_in_O <;> aesop

lemma oneSidedR_sat_down (LRO : Sequent)
    {Rcond : Finset Formula} (Rpreproof : Rcond ⊆ LRO.R)
    {Rres : Finset (Finset Formula)} (orule : OneSidedLocalRule Rcond Rres)
    {YS : Finset Sequent} (YS_def : YS = Finset.image (fun res => (∅, res, none)) Rres)
    {X : Finset Formula} (RX_sat : satisfiable (Sequent.right LRO ∪ X))
    : ∃ c ∈ applyLocalRule (LocalRule.oneSidedR orule YS_def) LRO, satisfiable (c.right ∪ X) := by
  rcases LRO with ⟨L,R,O⟩
  subst YS_def
  rcases RX_sat with ⟨W, M, w, satM⟩
  have : evaluate M w (con Rcond.sort) := by simp [conEval]; aesop
  have := (oneSidedLocalRuleTruth orule W M w).1 this
  rw [Finset.disconEval] at this
  rcases this with ⟨L', L'_in, w_L'⟩
  simp only [applyLocalRule, Finset.sdiff_empty, Finset.mem_image, exists_exists_and_eq_and,
    Finset.union_empty, Olf.change_old_none_none, Sequent.right_eq, Finset.union_assoc]
  refine ⟨L', L'_in, W, M, w, fun φ φ_in => ?_⟩
  specialize @satM φ
  simp only [Finset.mem_union, Finset.mem_sdiff] at φ_in
  rcases φ_in with φ_in_LnoCond | φ_in_L' | φ_in_O <;> aesop

-- Following four lemmas are almost the same, but then for the loaded diamond rules.

/-- Applying a `LoadRule` on the left will leave the right unchanged. -/
lemma loadedL_preserves_right {LRO : Sequent}
    (χ : LoadFormula) (Opreproof : LRO.O = some (Sum.inl (~'χ)))
    {ress} (lrule : LoadRule (~'χ) ress)
    {YS : Finset Sequent} (YS_def : YS = ress.image fun (X, o) => (X, ∅, o.map Sum.inl))
    : ∀ c ∈ applyLocalRule (LocalRule.loadedL χ lrule YS_def) LRO, c.right = LRO.right := by
  rcases LRO with ⟨L,R,O⟩
  cases Opreproof
  rintro ⟨L',R',O'⟩
  subst YS_def
  simp only [applyLocalRule, Finset.sdiff_empty, Olf.change_some_some_eq, Finset.mem_image,
    Prod.exists, ↓existsAndEq, and_true, Finset.union_empty, Sequent.right_eq, Olf.R_inl,
    forall_exists_index, and_imp] at *
  rintro _ olnlf _in_ress ⟨⟩
  rcases olnlf with _|⟨_⟩ <;> simp

/-- Applying a `LoadRule` on the right will leave the left unchanged. -/
lemma loadedR_preserves_left {LRO : Sequent}
    (χ : LoadFormula) (Opreproof : LRO.O = some (Sum.inr (~'χ)))
    {ress} (lrule : LoadRule (~'χ) ress)
    {YS : Finset Sequent} (YS_def : YS = ress.image fun (X, o) => (∅, X, o.map Sum.inr))
    : ∀ c ∈ applyLocalRule (LocalRule.loadedR χ lrule YS_def) LRO, c.left = LRO.left := by
  rcases LRO with ⟨L,R,O⟩
  cases Opreproof
  rintro ⟨L',R',O'⟩
  subst YS_def
  simp only [applyLocalRule, Finset.sdiff_empty, Olf.change_some_some_eq, Finset.mem_image,
    Prod.exists, ↓existsAndEq, and_true, Finset.union_empty, Sequent.left_eq, Olf.L_inr,
    forall_exists_index, and_imp] at *
  rintro _ olnlf _in_ress ⟨⟩
  rcases olnlf with _|⟨_⟩ <;> simp

/-- Applying a `LoadRule` on the left preserves satisfiability of the left,
even together with any other list of formulas as context. -/
lemma loadedL_sat_down (LRO : Sequent)
    (χ : LoadFormula) (Opreproof : LRO.O = some (Sum.inl (~'χ)))
    {ress} (lrule : LoadRule (~'χ) ress)
    {YS : Finset Sequent} (YS_def : YS = ress.image fun (X, o) => (X, ∅, o.map Sum.inl))
    {X : Finset Formula} (LX_sat : satisfiable (Sequent.left LRO ∪ X))
    : ∃ c ∈ applyLocalRule (LocalRule.loadedL χ lrule YS_def) LRO, satisfiable (c.left ∪ X) := by
  rcases LRO with ⟨L,R,O⟩
  cases Opreproof
  subst YS_def
  rcases LX_sat with ⟨W, M, w, satM⟩
  have w_nχ : evaluate M w (~χ.unload) := by apply satM; simp [Olf.L]
  have := (loadRuleTruth lrule W M w).1 w_nχ; clear w_nχ
  rw [disEval] at this
  simp only [Finset.mem_sort, Finset.mem_image, Function.comp_apply] at this
  rcases this with ⟨f, ⟨p, p_in, rfl⟩, w_f⟩
  rw [evaluate_con_sort] at w_f
  refine ⟨(L ∪ p.1, R ∪ ∅,
    Olf.change (some (Sum.inl (~'χ))) (some (Sum.inl (~'χ))) (p.2.map Sum.inl)), ?_, ?_⟩
  · simp only [applyLocalRule, Finset.mem_image]
    exact ⟨_, ⟨p, p_in, rfl⟩, by simp⟩
  · refine ⟨W, M, w, ?_⟩
    intro φ φ_in
    simp only [Sequent.left, Sequent.L_eq, Sequent.O_eq, Olf.change_some_some_eq,
      Finset.mem_union] at φ_in
    rcases φ_in with ((φ_in | φ_in) | φ_in) | φ_in
    · exact satM φ (by simp [Sequent.left, Sequent.L_eq, φ_in])
    · exact w_f φ (by rcases p with ⟨p1, _|nlf⟩ <;> simp [pairUnloadSet] <;> tauto)
    · rcases p with ⟨p1, _|nlf⟩
      · simp [Olf.L] at φ_in
      · simp only [Olf.L, Option.map_some, Finset.mem_singleton] at φ_in
        subst φ_in
        exact w_f _ (by simp [pairUnloadSet])
    · exact satM φ (by simp [φ_in])

/-- Applying a `LoadRule` on the right preserves satisfiability of the right,
even together with any other list of formulas as context. -/
lemma loadedR_sat_down (LRO : Sequent)
    (χ : LoadFormula) (Opreproof : LRO.O = some (Sum.inr (~'χ)))
    {ress} (lrule : LoadRule (~'χ) ress)
    {YS : Finset Sequent} (YS_def : YS = ress.image fun (X, o) => (∅, X, o.map Sum.inr))
    {X : Finset Formula} (RX_sat : satisfiable (Sequent.right LRO ∪ X))
    : ∃ c ∈ applyLocalRule (LocalRule.loadedR χ lrule YS_def) LRO, satisfiable (c.right ∪ X) := by
  rcases LRO with ⟨L,R,O⟩
  cases Opreproof
  subst YS_def
  rcases RX_sat with ⟨W, M, w, satM⟩
  have w_nχ : evaluate M w (~χ.unload) := by apply satM; simp [Olf.R]
  have := (loadRuleTruth lrule W M w).1 w_nχ; clear w_nχ
  rw [disEval] at this
  simp only [Finset.mem_sort, Finset.mem_image, Function.comp_apply] at this
  rcases this with ⟨f, ⟨p, p_in, rfl⟩, w_f⟩
  rw [evaluate_con_sort] at w_f
  refine ⟨(L ∪ ∅, R ∪ p.1,
    Olf.change (some (Sum.inr (~'χ))) (some (Sum.inr (~'χ))) (p.2.map Sum.inr)), ?_, ?_⟩
  · simp only [applyLocalRule, Finset.mem_image]
    exact ⟨_, ⟨p, p_in, rfl⟩, by simp⟩
  · refine ⟨W, M, w, ?_⟩
    intro φ φ_in
    simp only [Sequent.right, Sequent.R_eq, Sequent.O_eq, Olf.change_some_some_eq,
      Finset.mem_union] at φ_in
    rcases φ_in with ((φ_in | φ_in) | φ_in) | φ_in
    · exact satM φ (by simp [Sequent.right, Sequent.R_eq, φ_in])
    · exact w_f φ (by rcases p with ⟨p1, _|nlf⟩ <;> simp [pairUnloadSet] <;> tauto)
    · rcases p with ⟨p1, _|nlf⟩
      · simp [Olf.R] at φ_in
      · simp only [Olf.R, Option.map_some, Finset.mem_singleton] at φ_in
        subst φ_in
        exact w_f _ (by simp [pairUnloadSet])
    · exact satM φ (by simp [φ_in])

/-! ## Local Rule Applications -/

/-- A local rule application going from `⟨L,R,O⟩` to `C` consists of a
local rule `lr` replacing `⟨Lcond, Rcond, Ocond⟩` by `ress` and
proofs that `⟨Lcond, Rcond, Ocond⟩` is a subsequent of `⟨L,R,O⟩`
and that `C` are the results of applying `lr` to `⟨L,R,O⟩`. -/
structure LocalRuleApp where
    /-- The source sequent's left formula component. -/
    L : Finset Formula := by grind
    /-- The source sequent's right formula component. -/
    R : Finset Formula := by grind
    /-- The source sequent's optional loaded formula and its side. -/
    O : Olf := by grind
    /-- The left formulas required by the rule. -/
    Lcond : Finset Formula := {}
    /-- The right formulas required by the rule. -/
    Rcond : Finset Formula := {}
    /-- The optional loading required by the rule. -/
    Ocond : Olf := none
    /-- The result sequents supplied by the rule before applying source context. -/
    ress : Finset Sequent := by grind
    /-- The local rule connecting these preconditions and results. -/
    lr : LocalRule (Lcond, Rcond, Ocond) ress
    /-- The child sequents obtained by applying the rule to the source context. -/
    C : Finset Sequent := applyLocalRule lr (L,R,O)
    hC : C = applyLocalRule lr (L,R,O) := by rfl
    preconditionProof : Lcond ⊆ L ∧ Rcond ⊆ R ∧ Ocond ⊆ O
  deriving DecidableEq

/-- The source sequent of a local rule application. -/
@[simp]
abbrev LocalRuleApp.X (lra : LocalRuleApp) : Sequent := ⟨lra.L, lra.R, lra.O⟩

/-- The left loaded rule preserves satisfiability in both directions. -/
private theorem localRuleTruth_loadedL
    {W : Type} (M : KripkeModel W) (w : W)
    (L R : Finset Formula) (O : Olf) {ress : Finset Sequent}
    {outputs : Finset (Finset Formula × Option NegLoadFormula)}
    (χ : LoadFormula) (lrule : LoadRule (~'χ) outputs)
    (YS_def : ress = outputs.image (fun (X, o) => (X, ∅, o.map Sum.inl)))
    (C : Finset Sequent) (hC : C = applyLocalRule (.loadedL χ lrule YS_def) (L, R, O))
    (preconditionProof : ∅ ⊆ L ∧ ∅ ⊆ R ∧ some (Sum.inl (~'χ)) ⊆ O) :
    (∀ f ∈ Sequent.toFinset (L, R, O), evaluate M w f) ↔ ∃ Y ∈ C, (M, w) ⊨ Y := by
  obtain ⟨-, -, hO⟩ := preconditionProof
  rw [Option.some_subseteq] at hO
  subst hC; subst YS_def; cases hO
  constructor
  · intro hyp
    have w_nχ : evaluate M w (~χ.unload) := hyp _ (by simp [Sequent.toFinset])
    have := (loadRuleTruth lrule W M w).1 w_nχ
    rw [disEval] at this
    simp only [Finset.mem_sort, Finset.mem_image, Function.comp_apply] at this
    rcases this with ⟨f, ⟨p, p_in, rfl⟩, w_f⟩
    rw [evaluate_con_sort] at w_f
    refine ⟨(L ∪ p.1, R ∪ ∅,
      Olf.change (some (Sum.inl (~'χ))) (some (Sum.inl (~'χ))) (p.2.map Sum.inl)), ?_, ?_⟩
    · simp only [applyLocalRule, Finset.mem_image]
      exact ⟨_, ⟨p, p_in, rfl⟩, by simp⟩
    · have key : ∀ g ∈ Sequent.toFinset (L ∪ p.1, R ∪ ∅,
          Olf.change (some (Sum.inl (~'χ))) (some (Sum.inl (~'χ))) (p.2.map Sum.inl)),
          g ∈ Sequent.toFinset ((L, R, some (Sum.inl (~'χ))) : Sequent)
            ∨ g ∈ pairUnloadSet p := by
        rcases p with ⟨p1, _ | nlf⟩ <;> intro g hg <;>
          simp [Sequent.toFinset, pairUnloadSet] at hg ⊢ <;> tauto
      intro g g_in
      rcases key g g_in with h | h
      · exact hyp g h
      · exact w_f g h
  · rintro ⟨Ci, Ci_in, w_Ci⟩
    simp only [applyLocalRule, Finset.mem_image] at Ci_in
    rcases Ci_in with ⟨q, ⟨p, p_in, rfl⟩, rfl⟩
    have hsub : ∀ g ∈ pairUnloadSet p, evaluate M w g := by
      rcases p with ⟨p1, _ | nlf⟩ <;> intro g hg <;>
        exact w_Ci g (by simp [Sequent.toFinset, pairUnloadSet] at hg ⊢; tauto)
    intro g g_in
    simp only [Sequent.toFinset, Finset.mem_union] at g_in
    rcases g_in with (hg | hg) | hg
    · exact w_Ci g (by simp [Sequent.toFinset]; tauto)
    · exact w_Ci g (by simp [Sequent.toFinset]; tauto)
    · simp only [Option.map_some, Option.toFinset_some, Finset.mem_singleton, Sum.elim_inl,
        negUnload] at hg
      subst hg
      refine (loadRuleTruth lrule W M w).2 ?_
      rw [disEval]
      refine ⟨con ((pairUnloadSet p).sort fun a b => a ≤ b), ?_, ?_⟩
      · simp only [Finset.mem_sort, Finset.mem_image, Function.comp_apply]
        exact ⟨p, p_in, rfl⟩
      · rw [evaluate_con_sort]
        exact hsub

/-- Any local rule application is sound and invertible. -/
theorem localRuleTruth
    (lra : LocalRuleApp) {W} (M : KripkeModel W) (w : W)
  : (M,w) ⊨ lra.X ↔ ∃ Ci ∈ lra.C, (M,w) ⊨ Ci
  := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, preconditionProof⟩
  simp only [LocalRuleApp.X] at *
  cases rule
  case oneSidedL ress orule ress_def =>
    subst ress_def
    have osTruth := oneSidedLocalRuleTruth orule W M w
    subst hC
    simp only [Finset.empty_subset, Option.none_subseteq, and_self, and_true, applyLocalRule,
      Finset.sdiff_empty, Finset.mem_image, exists_exists_and_eq_and, Finset.union_empty,
      Olf.change_old_none_none] at *
    constructor
    · intro w_LRO
      have : evaluate M w (ress.pdlDiscon) := by
        rw [← osTruth, conEval]
        intro f f_in; apply w_LRO
        simp only [Sequent.toFinset, Finset.union_assoc, Finset.mem_union, Option.mem_toFinset,
          Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl, negUnload, Sum.elim_inr]
        exact Or.inl <| preconditionProof <| (Finset.mem_sort _).mp f_in
      rw [Finset.disconEval] at this
      rcases this with ⟨Y, Y_in, claim⟩
      use Y
      constructor
      · exact Y_in
      · intro f f_in
        simp only [Sequent.toFinset, Finset.mem_union, Finset.mem_sdiff] at f_in
        rcases f_in with ((⟨f_in_L, -⟩ | f_in_Y) | f_in_R) | f_in_O
        · exact w_LRO f (by simp only [Sequent.toFinset, Finset.mem_union]; tauto)
        · exact claim f f_in_Y
        · exact w_LRO f (by simp only [Sequent.toFinset, Finset.mem_union]; tauto)
        · exact w_LRO f (by simp only [Sequent.toFinset, Finset.mem_union]; tauto)
    · rintro ⟨Y, Y_in, w_LYRO⟩
      intro f f_in
      have hcond : ∀ g ∈ Lcond, evaluate M w g := by
        rw [← evaluate_con_sort, osTruth, Finset.disconEval]
        exact ⟨Y, Y_in, fun g hg =>
          w_LYRO g (by simp only [Sequent.toFinset, Finset.mem_union]; tauto)⟩
      simp only [Sequent.toFinset, Finset.mem_union] at f_in
      rcases f_in with (f_in_L | f_in_R) | f_in_O
      · rcases em (f ∈ Lcond) with f_in_cond | f_notin_cond
        · exact hcond f f_in_cond
        · exact w_LYRO f
            (by simp only [Sequent.toFinset, Finset.mem_union, Finset.mem_sdiff]; tauto)
      · exact w_LYRO f (by simp only [Sequent.toFinset, Finset.mem_union]; tauto)
      · exact w_LYRO f (by simp only [Sequent.toFinset, Finset.mem_union]; tauto)
  case oneSidedR ress orule ress_def =>
    subst ress_def
    -- based on oneSidedL case
    have osTruth := oneSidedLocalRuleTruth orule W M w
    subst hC
    simp only [Finset.empty_subset, Option.none_subseteq, and_true, true_and, applyLocalRule,
      Finset.sdiff_empty, Finset.mem_image, exists_exists_and_eq_and, Finset.union_empty,
      Olf.change_old_none_none] at *
    constructor
    · intro w_LRO
      have : evaluate M w (ress.pdlDiscon) := by
        rw [← osTruth, conEval]
        intro f f_in; apply w_LRO
        simp only [Sequent.toFinset, Finset.union_assoc, Finset.mem_union, Option.mem_toFinset,
          Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl, negUnload,
          Sum.elim_inr]
        exact Or.inr <| Or.inl <| preconditionProof <| (Finset.mem_sort _).mp f_in
      rw [Finset.disconEval] at this
      rcases this with ⟨Y, Y_in, claim⟩
      use Y
      constructor
      · exact Y_in
      · intro f f_in
        simp only [Sequent.toFinset, Finset.mem_union, Finset.mem_sdiff] at f_in
        rcases f_in with (f_in_L | (⟨f_in_R, -⟩ | f_in_Y)) | f_in_O
        · exact w_LRO f (by simp only [Sequent.toFinset, Finset.mem_union]; tauto)
        · exact w_LRO f (by simp only [Sequent.toFinset, Finset.mem_union]; tauto)
        · exact claim f f_in_Y
        · exact w_LRO f (by simp only [Sequent.toFinset, Finset.mem_union]; tauto)
    · rintro ⟨Y, Y_in, w_LYRO⟩
      intro f f_in
      have hcond : ∀ g ∈ Rcond, evaluate M w g := by
        rw [← evaluate_con_sort, osTruth, Finset.disconEval]
        exact ⟨Y, Y_in, fun g hg =>
          w_LYRO g (by simp only [Sequent.toFinset, Finset.mem_union]; tauto)⟩
      simp only [Sequent.toFinset, Finset.mem_union] at f_in
      rcases f_in with (f_in_L | f_in_R) | f_in_O
      · exact w_LYRO f (by simp only [Sequent.toFinset, Finset.mem_union]; tauto)
      · rcases em (f ∈ Rcond) with f_in_cond | f_notin_cond
        · exact hcond f f_in_cond
        · exact w_LYRO f
            (by simp only [Sequent.toFinset, Finset.mem_union, Finset.mem_sdiff]; tauto)
      · exact w_LYRO f (by simp only [Sequent.toFinset, Finset.mem_union]; tauto)
  case LRnegL ϕ =>
    obtain ⟨hL, hR, -⟩ := preconditionProof
    subst hC
    simp only [applyLocalRule, Finset.image_empty, Finset.notMem_empty, false_and, exists_false,
      iff_false]
    intro hyp
    have h1 := hyp ϕ (by
      simp only [Sequent.toFinset, Finset.mem_union]; exact Or.inl (Or.inl (hL (by simp))))
    have h2 := hyp (~ϕ) (by
      simp only [Sequent.toFinset, Finset.mem_union]; exact Or.inl (Or.inr (hR (by simp))))
    simp only [evaluate] at h2
    exact h2 h1
  case LRnegR ϕ =>
    obtain ⟨hL, hR, -⟩ := preconditionProof
    subst hC
    simp only [applyLocalRule, Finset.image_empty, Finset.notMem_empty, false_and, exists_false,
      iff_false]
    intro hyp
    have h1 := hyp (~ϕ) (by
      simp only [Sequent.toFinset, Finset.mem_union]; exact Or.inl (Or.inl (hL (by simp))))
    have h2 := hyp ϕ (by
      simp only [Sequent.toFinset, Finset.mem_union]; exact Or.inl (Or.inr (hR (by simp))))
    simp only [evaluate] at h1
    exact h1 h2
  case loadedL ress χ lrule YS_def =>
    exact localRuleTruth_loadedL M w L R O χ lrule YS_def C hC preconditionProof
  case loadedR ress χ lrule YS_def =>
    obtain ⟨-, -, hO⟩ := preconditionProof
    rw [Option.some_subseteq] at hO
    subst hC; subst YS_def; cases hO
    constructor
    · intro hyp
      have w_nχ : evaluate M w (~χ.unload) := hyp _ (by simp [Sequent.toFinset])
      have := (loadRuleTruth lrule W M w).1 w_nχ
      rw [disEval] at this
      simp only [Finset.mem_sort, Finset.mem_image, Function.comp_apply] at this
      rcases this with ⟨f, ⟨p, p_in, rfl⟩, w_f⟩
      rw [evaluate_con_sort] at w_f
      refine ⟨(L ∪ ∅, R ∪ p.1,
        Olf.change (some (Sum.inr (~'χ))) (some (Sum.inr (~'χ))) (p.2.map Sum.inr)), ?_, ?_⟩
      · simp only [applyLocalRule, Finset.mem_image]
        exact ⟨_, ⟨p, p_in, rfl⟩, by simp⟩
      · have key : ∀ g ∈ Sequent.toFinset (L ∪ ∅, R ∪ p.1,
            Olf.change (some (Sum.inr (~'χ))) (some (Sum.inr (~'χ))) (p.2.map Sum.inr)),
            g ∈ Sequent.toFinset ((L, R, some (Sum.inr (~'χ))) : Sequent)
              ∨ g ∈ pairUnloadSet p := by
          rcases p with ⟨p1, _ | nlf⟩ <;> intro g hg <;>
            simp [Sequent.toFinset, pairUnloadSet] at hg ⊢ <;> tauto
        intro g g_in
        rcases key g g_in with h | h
        · exact hyp g h
        · exact w_f g h
    · rintro ⟨Ci, Ci_in, w_Ci⟩
      simp only [applyLocalRule, Finset.mem_image] at Ci_in
      rcases Ci_in with ⟨q, ⟨p, p_in, rfl⟩, rfl⟩
      have hsub : ∀ g ∈ pairUnloadSet p, evaluate M w g := by
        rcases p with ⟨p1, _ | nlf⟩ <;> intro g hg <;>
          exact w_Ci g (by simp [Sequent.toFinset, pairUnloadSet] at hg ⊢; tauto)
      intro g g_in
      simp only [Sequent.toFinset, Finset.mem_union] at g_in
      rcases g_in with (hg | hg) | hg
      · exact w_Ci g (by simp [Sequent.toFinset]; tauto)
      · exact w_Ci g (by simp [Sequent.toFinset]; tauto)
      · simp only [Option.map_some, Option.toFinset_some, Finset.mem_singleton, Sum.elim_inr,
          negUnload] at hg
        subst hg
        refine (loadRuleTruth lrule W M w).2 ?_
        rw [disEval]
        refine ⟨con ((pairUnloadSet p).sort fun a b => a ≤ b), ?_, ?_⟩
        · simp only [Finset.mem_sort, Finset.mem_image, Function.comp_apply]
          exact ⟨p, p_in, rfl⟩
        · rw [evaluate_con_sort]
          exact hsub

/-- If we can apply a local rule to a sequent then it cannot be basic. -/
lemma nonbasic_of_localRuleApp (lra : LocalRuleApp) : ¬ lra.X.basic := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, preconditionProof⟩
  unfold Sequent.basic
  simp only
  rw [and_iff_not_or_not]
  simp only [not_not]
  cases rule
  case oneSidedL ress orule ress_def =>
    subst_eqs
    cases orule
    case bot => right; simp_all [Sequent.closed]; tauto
    case not φ =>
      right; simp_all only [Sequent.closed, LocalRuleApp.X, Sequent.mem_def, Sequent.L_eq,
        Sequent.R_eq]; right
      refine ⟨φ, Or.inl ?_, Or.inl ?_⟩ <;> grind
    case neg φ =>
      left; push Not; simp_all only [Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
        Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
        negUnload, Sum.elim_inr, Formula.basic, decide_false, decide_true, ne_eq,
        Bool.not_eq_true]
      refine ⟨~~φ, Or.inl (by simp_all), by simp⟩
    case con φ1 φ2 =>
      left; push Not; simp_all only [Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
        Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
        negUnload, Sum.elim_inr, Formula.basic, decide_false, decide_true, ne_eq,
        Bool.not_eq_true]
      refine ⟨φ1 ⋀ φ2, Or.inl (by simp_all), by simp⟩
    case nCo φ1 φ2 =>
      left; push Not; simp_all only [Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
        Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
        negUnload, Sum.elim_inr, Formula.basic, decide_false, decide_true, ne_eq,
        Bool.not_eq_true]
      refine ⟨~(φ1 ⋀ φ2), Or.inl (by simp_all), by simp⟩
    case box α φ α_nonAtom =>
      left; push Not; simp_all only [Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
        Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
        negUnload, Sum.elim_inr, Formula.basic, decide_false, decide_true, ne_eq,
        Bool.not_eq_true]
      refine ⟨⌈α⌉φ, Or.inl (by simp_all), ?_⟩
      cases α <;> simp_all; simp [Program.isAtomic] at α_nonAtom
    case dia α φ α_nonAtom =>
      left; push Not; simp_all only [Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
        Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
        negUnload, Sum.elim_inr, Formula.basic, decide_false, decide_true, ne_eq,
        Bool.not_eq_true]
      refine ⟨~⌈α⌉φ, Or.inl ?_, ?_⟩
      · apply preconditionProof.1; simp
      · cases α <;> simp_all; simp [Program.isAtomic] at α_nonAtom
  case oneSidedR ress orule ress_def => -- analogous to oneSidedL
    cases orule
    case bot => right; simp_all [Sequent.closed]; tauto
    case not φ =>
      right; simp_all only [Sequent.closed, LocalRuleApp.X, Sequent.mem_def, Sequent.L_eq,
        Sequent.R_eq]; right
      refine ⟨φ, Or.inr ?_, Or.inr ?_⟩ <;> grind
    case neg φ =>
      left; push Not; simp_all only [Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
        Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
        negUnload, Sum.elim_inr, Formula.basic, decide_false, decide_true, ne_eq,
        Bool.not_eq_true]
      refine ⟨~~φ, Or.inr (by simp_all), by simp⟩
    case con φ1 φ2 =>
      left; push Not; simp_all only [Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
        Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
        negUnload, Sum.elim_inr, Formula.basic, decide_false, decide_true, ne_eq,
        Bool.not_eq_true]
      refine ⟨φ1 ⋀ φ2, Or.inr (by simp_all), by simp⟩
    case nCo φ1 φ2 =>
      left; push Not; simp_all only [Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
        Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
        negUnload, Sum.elim_inr, Formula.basic, decide_false, decide_true, ne_eq,
        Bool.not_eq_true]
      refine ⟨~(φ1 ⋀ φ2), Or.inr (by simp_all), by simp⟩
    case box α φ α_nonAtom =>
      left; push Not; simp_all only [Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
        Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
        negUnload, Sum.elim_inr, Formula.basic, decide_false, decide_true, ne_eq,
        Bool.not_eq_true]
      refine ⟨⌈α⌉φ, Or.inr (by simp_all), ?_⟩
      cases α <;> simp_all; simp [Program.isAtomic] at α_nonAtom
    case dia α φ α_nonAtom =>
      left; push Not; simp_all only [Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
        Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
        negUnload, Sum.elim_inr, Formula.basic, decide_false, decide_true, ne_eq,
        Bool.not_eq_true]
      refine ⟨~⌈α⌉φ, Or.inr (Or.inl ?_), ?_⟩
      · apply preconditionProof.2.1; simp
      · cases α <;> simp_all; simp [Program.isAtomic] at α_nonAtom
  case LRnegL =>
    right
    simp [Sequent.closed]
    aesop
  case LRnegR =>
    right
    simp [Sequent.closed]
    aesop
  case loadedL ress χ lrule ress_def =>
    obtain ⟨-, -, hO⟩ := preconditionProof
    rw [Option.some_subseteq] at hO
    cases hO
    left
    push Not
    refine ⟨~χ.unload, by simp [Sequent.toFinset], ?_⟩
    cases lrule
    case dia α ξ α_nonAtom => cases α <;> simp [Program.isAtomic] at α_nonAtom ⊢
    case dia' α φ α_nonAtom => cases α <;> simp [Program.isAtomic] at α_nonAtom ⊢
  case loadedR ress χ lrule ress_def => -- analogous to loadedL
    obtain ⟨-, -, hO⟩ := preconditionProof
    rw [Option.some_subseteq] at hO
    cases hO
    left
    push Not
    refine ⟨~χ.unload, by simp [Sequent.toFinset], ?_⟩
    cases lrule
    case dia α ξ α_nonAtom => cases α <;> simp [Program.isAtomic] at α_nonAtom ⊢
    case dia' α φ α_nonAtom => cases α <;> simp [Program.isAtomic] at α_nonAtom ⊢

/-- For a given non-basic formula in the left list `L`,
construct a `LocalRuleApp` using an appropriate `OneSidedLocalRule`. -/
def localRuleAppOfNonbasicInL (L R : Finset Formula) (O : Olf) (f : Formula)
    (f_in : f ∈ L) (f_nonBas : f.basic = false)
    : { lra : LocalRuleApp // lra.X = (L, R, O) } :=
match f with
  | .bottom => ⟨{ L, R, O, Lcond := {⊥}, ress := {}
                  lr := .oneSidedL .bot rfl
                  preconditionProof := by simp_all [Bot.bot]}, rfl⟩
  | ·n => by simp [Formula.basic] at f_nonBas
  | .neg f' => match f' with
    | .bottom => by simp [Formula.basic] at f_nonBas
    | .atom_prop n => by simp [Formula.basic] at f_nonBas
    | .neg φ => ⟨{L, R, O, Lcond := {~~φ}, ress := {({φ}, {}, none)}
                  lr := .oneSidedL (.neg φ) rfl
                  preconditionProof := by simp_all}, rfl⟩
    | .and φ ψ => ⟨{L, R, O, Lcond := {~(φ⋀ψ)}
                    ress := {({~φ}, {}, none), ({~ψ}, {}, none)}
                    lr := .oneSidedL (.nCo φ ψ) (by simp_all)
                    preconditionProof := by simp_all}, rfl⟩
    | .box α φ =>
        have hna : ¬ α.isAtomic := by cases α <;> simp_all [Formula.basic, Program.isAtomic]
        ⟨{L, R, O, Lcond := {~⌈α⌉φ}
          ress := ((unfoldDiamond α φ).pdlToFinFin.image (fun res => (res, {}, none)))
          lr := .oneSidedL (.dia α φ hna) rfl
          preconditionProof := by simp_all}, rfl⟩
  | .and φ ψ => ⟨{L, R, O, Lcond := {φ⋀ψ}, ress := {({φ,ψ}, {}, none)}
                  lr := .oneSidedL (.con φ ψ) rfl
                  preconditionProof := by simp_all}, rfl⟩
  | .box α φ =>
      have hna : ¬ α.isAtomic := by cases α <;> simp_all [Formula.basic, Program.isAtomic]
      ⟨{L, R, O, Lcond := {⌈α⌉φ}
        ress := (unfoldBox α φ).pdlToFinFin.image (fun res => (res, {}, none))
        lr := .oneSidedL (.box α φ hna) rfl
        preconditionProof := by simp_all}, rfl⟩

/-- For a given non-basic formula in the right list `R`,
construct a `LocalRuleApp` using an appropriate `OneSidedLocalRule`. -/
def localRuleAppOfNonbasicInR (L R : Finset Formula) (O : Olf) (f : Formula)
    (f_in : f ∈ R) (f_nonBas : f.basic = false)
    : { lra : LocalRuleApp // lra.X = (L, R, O) } :=
  match f with
  | .bottom => ⟨{ L, R, O, Rcond := {⊥}, ress := {}
                  lr := .oneSidedR .bot rfl
                  preconditionProof := by simp_all [Bot.bot]}, rfl⟩
  | .atom_prop n => by simp [Formula.basic] at f_nonBas
  | .neg f' => match f' with
    | .bottom => by simp [Formula.basic] at f_nonBas
    | .atom_prop n => by simp [Formula.basic] at f_nonBas
    | .neg φ =>
            ⟨{L, R, O, Rcond := {~~φ}, ress := {({}, {φ}, none)}
              lr := .oneSidedR (.neg φ) rfl
              preconditionProof := by simp_all }, rfl⟩
    | .and φ ψ =>
            ⟨{L, R, O, Rcond := {~(φ⋀ψ)}
              ress := {({}, {~φ}, none), ({}, {~ψ}, none)}
              lr := .oneSidedR (.nCo φ ψ) (by simp_all)
              preconditionProof := by simp_all }, rfl⟩
    | .box α φ =>
          have hna : ¬ α.isAtomic := by
            cases α <;> simp_all [Formula.basic, Program.isAtomic]
          ⟨{L, R, O, Rcond := {~⌈α⌉φ}
            ress := (unfoldDiamond α φ).pdlToFinFin.image (fun res => ({}, res, none))
            lr := .oneSidedR (.dia α φ hna) rfl
            preconditionProof := by simp_all }, rfl⟩
  | .and φ ψ => ⟨{L, R, O, Rcond := {φ⋀ψ}, ress := {({}, {φ,ψ}, none)}
                  lr := .oneSidedR (.con φ ψ) rfl
                  preconditionProof := by simp_all }, rfl⟩
  | .box α φ =>
    have hna : ¬ α.isAtomic := by cases α <;> simp_all [Formula.basic, Program.isAtomic]
    ⟨{L, R, O, Rcond := {⌈α⌉φ}
      ress := (unfoldBox α φ).pdlToFinFin.image (fun res => ({}, res, none))
      lr := .oneSidedR (.box α φ hna) rfl
      preconditionProof := by simp_all }, rfl⟩

/-- A sequent is basic iff no local rule can be applied.
Note that in the paper (L+) and (L-) are also local rules and had to be excluded
here, but here in the Lean formalization they are `PdlRule`s anyway. -/
lemma basic_iff_noLocalRuleApp {Y : Sequent} :
    Y.basic ↔ ¬ ∃ (lra : LocalRuleApp),lra.X = Y := by
  constructor
  · have := nonbasic_of_localRuleApp
    grind
  · intro no_lra
    by_contra Y_nonbas
    unfold Sequent.basic at Y_nonbas
    have not_closed : ¬ Sequent.closed Y := by
      clear Y_nonbas
      intro Y_closed
      absurd no_lra
      rcases Y_closed with bot_in_Y | f_not_f_in_Y
      · rcases Y with ⟨L,R,O⟩
        simp only [LocalRuleApp.X, not_exists, Sequent.mem_def, Sequent.L_eq, Sequent.R_eq] at *
        cases bot_in_Y
        · exact ⟨⟨L,R,O, {⊥},{},none, {}, .oneSidedL .bot rfl, {}, rfl, by simp_all⟩, by simp⟩
        · exact ⟨⟨L,R,O, {},{⊥},none, {}, .oneSidedR .bot rfl, {}, rfl, by simp_all⟩, by simp⟩
      · rcases f_not_f_in_Y with ⟨φ, φ_in, not_φ_in⟩
        rcases Y with ⟨L,R,O⟩
        simp only [LocalRuleApp.X, not_exists, Sequent.mem_def, Sequent.L_eq, Sequent.R_eq] at *
        cases φ_in <;> cases not_φ_in
        · refine ⟨⟨L,R,O, {φ, ~φ}, {}, none, {}, .oneSidedL (.not _) rfl, {}, rfl, ?_⟩, by simp⟩
          simp_all; grind
        · exact ⟨⟨L,R,O, {φ}, {~φ}, none, {}, LocalRule.LRnegL φ, {}, rfl, by simp_all⟩, by simp⟩
        · exact ⟨⟨L,R,O, {~φ}, {φ}, none, {}, LocalRule.LRnegR φ, {}, rfl, by simp_all⟩, by simp⟩
        · refine ⟨⟨L,R,O, {}, {φ, ~φ}, none, {}, .oneSidedR (.not _) rfl, {}, rfl, ?_⟩, by simp⟩
          simp_all; grind
    rcases Y with ⟨L,R,O⟩
    simp_all only [LocalRuleApp.X, not_exists, Sequent.toFinset, Finset.union_assoc,
      Finset.mem_union, Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists,
      Sum.elim_inl, negUnload, Sum.elim_inr, Formula.basic, decide_false, decide_true,
      not_false_eq_true, and_true, not_forall,  Bool.not_eq_true]
    clear not_closed
    absurd no_lra
    push Not
    -- Y_nonbas: ∃ formula in L ∪ R ∪ O that's not basic
    rcases Y_nonbas with ⟨f, f_where, f_nonBas⟩
    rcases f_where with f_in_L | f_in_R | ⟨a, rfl, rfl⟩ | ⟨b, rfl, rfl⟩
    · exact Subtype.exists_of_subtype <| localRuleAppOfNonbasicInL L R O f f_in_L f_nonBas
    · exact Subtype.exists_of_subtype <| localRuleAppOfNonbasicInR L R O f f_in_R f_nonBas
    · -- O = some (Sum.inl a), formula is ~a.1.unload, not basic
      -- a : NegLoadFormula, a = ~'χ where χ : LoadFormula = ⌊α⌋af
      rcases a with ⟨⟨α, af⟩⟩
      cases af with
      | normal φ =>
        -- formula is ~⌈α⌉φ, not basic means α is not atomic
        have hna : ¬ α.isAtomic := by
          cases α <;> simp_all [LoadFormula.unload, Program.isAtomic]
        exact ⟨{ L, R, O := some (Sum.inl (~'⌊α⌋(AnyFormula.normal φ)))
                 Ocond := some (Sum.inl (~'⌊α⌋(AnyFormula.normal φ)))
                 ress := (unfoldDiamondLoaded' α φ).pdlToFinFinOpt.image
                   (fun (X, o) => (X, {}, o.map Sum.inl))
                 lr := .loadedL _ (.dia' hna) rfl
                 preconditionProof := by simp }, rfl⟩
      | loaded χ =>
        have hna : ¬ α.isAtomic := by
          cases α <;> simp_all [LoadFormula.unload, Program.isAtomic]
        exact ⟨{ L, R, O := some (Sum.inl (~'⌊α⌋(AnyFormula.loaded χ)))
                 Ocond := some (Sum.inl (~'⌊α⌋(AnyFormula.loaded χ)))
                 ress := (unfoldDiamondLoaded α χ).pdlToFinFinOpt.image
                   (fun (X, o) => (X, {}, o.map Sum.inl))
                 lr := .loadedL _ (.dia hna) rfl
                 preconditionProof := by simp }, rfl⟩
    · -- O = some (Sum.inr b), symmetric to inl case
      rcases b with ⟨⟨α, af⟩⟩
      cases af with
      | normal φ =>
        have hna : ¬ α.isAtomic := by cases α <;> simp_all [LoadFormula.unload, Program.isAtomic]
        exact ⟨{ L, R, O := some (Sum.inr (~'⌊α⌋(AnyFormula.normal φ)))
                 Ocond := some (Sum.inr (~'⌊α⌋(AnyFormula.normal φ)))
                 ress := (unfoldDiamondLoaded' α φ).pdlToFinFinOpt.image
                   (fun (X, o) => ({}, X, o.map Sum.inr))
                 lr := .loadedR _ (.dia' hna) rfl
                 preconditionProof := by simp }, rfl⟩
      | loaded χ =>
        have hna : ¬ α.isAtomic := by cases α <;> simp_all [LoadFormula.unload, Program.isAtomic]
        exact ⟨{ L, R, O := some (Sum.inr (~'⌊α⌋(AnyFormula.loaded χ)))
                 Ocond := some (Sum.inr (~'⌊α⌋(AnyFormula.loaded χ)))
                 ress := (unfoldDiamondLoaded α χ).pdlToFinFinOpt.image
                   (fun (X, o) => ({}, X, o.map Sum.inr))
                 lr := .loadedR _ (.dia hna) rfl
                 preconditionProof := by simp }, rfl⟩

/-! ## Local rule applications preserve atomic formulas -/

lemma LocalRuleApp.preserve_bottom_down (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, ⊥ ∈ lra.X.toFinset → ⊥ ∈ Y.toFinset := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  subst hC
  cases rule <;> simp_all only [applyLocalRule, Finset.sdiff_empty, Finset.mem_image,
    exists_exists_and_eq_and, Finset.union_empty, Olf.change_old_none_none, Sequent.toFinset,
    Finset.union_assoc, Finset.mem_union, Option.mem_toFinset, Option.mem_def,
    Option.map_eq_some_iff, Sum.exists, Sum.elim_inl, negUnload, reduceCtorEq, and_false,
    exists_false, Sum.elim_inr, or_self, or_false, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Finset.mem_sdiff, Finset.image_empty, Finset.notMem_empty,
    exists_const_iff, and_true, IsEmpty.forall_iff, implies_true, Prod.exists, ↓existsAndEq]
  case oneSidedL ress orule ress_def => cases orule <;> simp_all <;> grind
  case oneSidedR ress orule ress_def => cases orule <;> simp_all <;> grind
  case loadedL ress chi lrule ress_def => cases lrule <;> simp_all only [Finset.empty_subset,
    Option.some_subseteq, true_and, List.pdlToFinFinOpt, List.mem_toFinset, List.mem_map,
    Prod.mk.injEq, Prod.exists, exists_eq_right_right, forall_exists_index, and_imp] <;>
    intros <;> subst_eqs <;> simp_all <;> grind
  case loadedR ress chi lrule ress_def => cases lrule <;> simp_all only [Finset.empty_subset,
    Option.some_subseteq, true_and, List.pdlToFinFinOpt, List.mem_toFinset, List.mem_map,
    Prod.mk.injEq, Prod.exists, exists_eq_right_right, forall_exists_index, and_imp] <;>
    intros <;> subst_eqs <;> simp_all <;> grind

lemma LocalRuleApp.preserve_atom_down (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, ∀ p : Nat,
      Formula.atom_prop p ∈ lra.X.toFinset → Formula.atom_prop p ∈ Y.toFinset := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  subst hC
  cases rule <;> simp_all only [applyLocalRule, Finset.sdiff_empty, Finset.mem_image,
    exists_exists_and_eq_and, Finset.union_empty, Olf.change_old_none_none, Sequent.toFinset,
    Finset.union_assoc, Finset.mem_union, Option.mem_toFinset, Option.mem_def,
    Option.map_eq_some_iff, Sum.exists, Sum.elim_inl, negUnload, reduceCtorEq, and_false,
    exists_false, Sum.elim_inr, or_self, or_false, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Finset.mem_sdiff, Finset.image_empty, Finset.notMem_empty,
    exists_const_iff, and_true, not_isEmpty_of_nonempty, IsEmpty.forall_iff, implies_true,
    Prod.exists, ↓existsAndEq]
  case oneSidedL ress orule ress_def => cases orule <;> simp_all <;> grind
  case oneSidedR ress orule ress_def => cases orule <;> simp_all <;> grind
  case loadedL ress chi lrule ress_def =>
    cases lrule <;> simp_all only [Finset.empty_subset, Option.some_subseteq, true_and,
      List.pdlToFinFinOpt, List.mem_toFinset, List.mem_map, Prod.mk.injEq, Prod.exists,
      exists_eq_right_right, forall_exists_index, and_imp] <;> intros <;> subst_eqs <;> simp_all
        <;> grind
  case loadedR ress chi lrule ress_def =>
    cases lrule <;> simp_all only [Finset.empty_subset, Option.some_subseteq, true_and,
      List.pdlToFinFinOpt, List.mem_toFinset, List.mem_map, Prod.mk.injEq, Prod.exists,
      exists_eq_right_right, forall_exists_index, and_imp] <;> intros <;> subst_eqs <;> simp_all
        <;> grind

lemma LocalRuleApp.preserve_neg_atom_down (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, ∀ p : Nat,
      (~(Formula.atom_prop p)) ∈ lra.X.toFinset → (~(Formula.atom_prop p)) ∈ Y.toFinset := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  subst hC
  cases rule <;> simp_all only [applyLocalRule, Finset.sdiff_empty, Finset.mem_image,
    exists_exists_and_eq_and, Finset.union_empty, Olf.change_old_none_none, Sequent.toFinset,
    Finset.union_assoc, Finset.mem_union, Option.mem_toFinset, Option.mem_def,
    Option.map_eq_some_iff, Sum.exists, Sum.elim_inl, negUnload, Formula.neg.injEq, Sum.elim_inr,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Finset.mem_sdiff, Finset.image_empty,
    Finset.notMem_empty, not_isEmpty_of_nonempty, IsEmpty.forall_iff, implies_true, Prod.exists,
    ↓existsAndEq, and_true]
  case oneSidedL ress orule ress_def => cases orule <;> grind
  case oneSidedR ress orule ress_def => cases orule <;> grind
  case loadedL ress chi lrule ress_def =>
    cases lrule <;> simp_all only [Finset.empty_subset, Option.some_subseteq, true_and,
      List.pdlToFinFinOpt, List.mem_toFinset, List.mem_map, Prod.mk.injEq, Prod.exists,
      exists_eq_right_right, forall_exists_index, and_imp] <;> intros <;> subst_eqs <;> simp_all
        <;> grind
  case loadedR ress chi lrule ress_def =>
    cases lrule <;> simp_all only [Finset.empty_subset, Option.some_subseteq, true_and,
      List.pdlToFinFinOpt, List.mem_toFinset, List.mem_map, Prod.mk.injEq, Prod.exists,
      exists_eq_right_right, forall_exists_index, and_imp] <;> intros <;> subst_eqs <;> simp_all
        <;> grind

lemma LocalRuleApp.preserve_local_atom_down (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, ∀ f,
      (f = ⊥ ∨ ∃ p : Nat, f = (Formula.atom_prop p) ∨ f = (~(Formula.atom_prop p))) →
      f ∈ lra.X.toFinset → f ∈ Y.toFinset := by
  rintro Y Y_in f (rfl | ⟨p, rfl | rfl⟩) f_in
  · exact lra.preserve_bottom_down Y Y_in f_in
  · exact lra.preserve_atom_down Y Y_in p f_in
  · exact lra.preserve_neg_atom_down Y Y_in p f_in

lemma mem_child_left_of_pairUnload_mem {w : List Formula} {o : Option NegLoadFormula}
    {f : Formula} (h : f ∈ pairUnload (w, o)) :
    f ∈ w ∨ f ∈ Olf.L (o.map Sum.inl) := by
  cases o <;> simp_all [pairUnload]

lemma mem_child_right_of_pairUnload_mem {w : List Formula} {o : Option NegLoadFormula}
    {f : Formula} (h : f ∈ pairUnload (w, o)) :
    f ∈ w ∨ f ∈ Olf.R (o.map Sum.inr) := by
  cases o <;> simp_all [pairUnload]

lemma loaded_unfold_child_closes_left {α : Program} {χ : LoadFormula}
    {w : List Formula} {o : Option NegLoadFormula}
    (h : (w, o) ∈ unfoldDiamondLoaded α χ) :
    ∃ Fδ ∈ Dset α, ∀ f ∈ Yset Fδ χ.unload,
      f ∈ w ∨ f ∈ Olf.L (o.map Sum.inl) := by
  have hm : pairUnload (w, o) ∈ unfoldDiamond α χ.unload := by
    rw [← unfoldDiamondLoaded_eq]
    exact List.mem_map_of_mem h
  simp only [unfoldDiamond, List.mem_map] at hm
  rcases hm with ⟨Fδ, Fδ_in, heq⟩
  exact ⟨Fδ, Fδ_in, fun f hf => mem_child_left_of_pairUnload_mem (heq ▸ hf)⟩

lemma loaded_unfold'_child_closes_left {α : Program} {φ : Formula}
    {w : List Formula} {o : Option NegLoadFormula}
    (h : (w, o) ∈ unfoldDiamondLoaded' α φ) :
    ∃ Fδ ∈ Dset α, ∀ f ∈ Yset Fδ φ,
      f ∈ w ∨ f ∈ Olf.L (o.map Sum.inl) := by
  have hm : pairUnload (w, o) ∈ unfoldDiamond α φ := by
    rw [← unfoldDiamondLoaded'_eq]
    exact List.mem_map_of_mem h
  simp only [unfoldDiamond, List.mem_map] at hm
  rcases hm with ⟨Fδ, Fδ_in, heq⟩
  exact ⟨Fδ, Fδ_in, fun f hf => mem_child_left_of_pairUnload_mem (heq ▸ hf)⟩

lemma loaded_unfold_child_closes_right {α : Program} {χ : LoadFormula}
    {w : List Formula} {o : Option NegLoadFormula}
    (h : (w, o) ∈ unfoldDiamondLoaded α χ) :
    ∃ Fδ ∈ Dset α, ∀ f ∈ Yset Fδ χ.unload,
      f ∈ w ∨ f ∈ Olf.R (o.map Sum.inr) := by
  have hm : pairUnload (w, o) ∈ unfoldDiamond α χ.unload := by
    rw [← unfoldDiamondLoaded_eq]
    exact List.mem_map_of_mem h
  simp only [unfoldDiamond, List.mem_map] at hm
  rcases hm with ⟨Fδ, Fδ_in, heq⟩
  exact ⟨Fδ, Fδ_in, fun f hf => mem_child_right_of_pairUnload_mem (heq ▸ hf)⟩

lemma loaded_unfold'_child_closes_right {α : Program} {φ : Formula}
    {w : List Formula} {o : Option NegLoadFormula}
    (h : (w, o) ∈ unfoldDiamondLoaded' α φ) :
    ∃ Fδ ∈ Dset α, ∀ f ∈ Yset Fδ φ,
      f ∈ w ∨ f ∈ Olf.R (o.map Sum.inr) := by
  have hm : pairUnload (w, o) ∈ unfoldDiamond α φ := by
    rw [← unfoldDiamondLoaded'_eq]
    exact List.mem_map_of_mem h
  simp only [unfoldDiamond, List.mem_map] at hm
  rcases hm with ⟨Fδ, Fδ_in, heq⟩
  exact ⟨Fδ, Fδ_in, fun f hf => mem_child_right_of_pairUnload_mem (heq ▸ hf)⟩

/-- Preservation and expansion for a local rule acting on the L component. -/
private theorem formulaExpansion_oneSidedL
    {Y : Sequent} (L R : Finset Formula) (O : Olf) {Lcond : Finset Formula}
    {ress : Finset Sequent} {outputs : Finset (Finset Formula)}
    (orule : OneSidedLocalRule Lcond outputs) (pre : Lcond ⊆ L ∧ ∅ ⊆ R ∧ none ⊆ O)
    (YS_def : ress = outputs.image (fun res => (res, ∅, none)))
    (hY : Y ∈ applyLocalRule (.oneSidedL orule YS_def) (L, R, O)) : ∀ f ∈ Sequent.toFinset (L, R,
      O),
      f ∈ Y.toFinset ∨
        (∀ (φ ψ : Formula) (α : Program),
          (f = (~~φ) → φ ∈ Y.toFinset) ∧
          (f = (φ⋀ψ) → φ ∈ Y.toFinset ∧ ψ ∈ Y.toFinset) ∧
          (f = (~(φ⋀ψ)) → (~φ) ∈ Y.toFinset ∨ (~ψ) ∈ Y.toFinset) ∧
          (f = (⌈α⌉φ) → ∃ l : TP α, (Bset α l φ).all (· ∈ Y.toFinset)) ∧
          (f = (~⌈α⌉φ) → ∃ Fδ ∈ Dset α, (Yset Fδ φ).all (· ∈ Y.toFinset))) := by
  subst YS_def
  cases orule
  case neg φ =>
    simp_all only [applyLocalRule, Finset.sdiff_empty, Finset.image_singleton,
      Finset.union_singleton, Finset.union_empty, Olf.change_old_none_none,
      Finset.mem_singleton, Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
      Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
      negUnload, Sum.elim_inr, Finset.insert_union, Finset.mem_insert, Finset.mem_sdiff,
      Formula.neg.injEq, List.all_eq_true, Prod.exists]
    intro f hf
    by_cases hp : f = ~~φ
    · subst f; right; simp
    · left
      rcases hf with hf | hf | hf | hf
      all_goals aesop
  case con φ ψ =>
    simp_all only [applyLocalRule, Finset.sdiff_empty, Finset.image_singleton,
      Finset.union_insert, Finset.union_singleton, Finset.union_empty, Olf.change_old_none_none,
      Finset.mem_singleton, Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
      Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
      negUnload, Sum.elim_inr, Finset.insert_union, Finset.mem_insert, Finset.mem_sdiff,
      reduceCtorEq, not_false_eq_true, and_true, Formula.neg.injEq, List.all_eq_true,
      Prod.exists]
    intro f hf
    by_cases hp : f = φ⋀ψ
    · subst f; right; simp
    · left
      rcases hf with hf | hf | hf | hf
      all_goals aesop
  case nCo φ ψ =>
    simp_all only [applyLocalRule, Finset.sdiff_empty, Finset.image_insert,
      Finset.image_singleton, Finset.union_singleton, Finset.union_empty,
      Olf.change_old_none_none, Finset.mem_insert, Finset.mem_singleton, Sequent.toFinset,
      Finset.union_assoc, Finset.mem_union, Option.mem_toFinset, Option.mem_def,
      Option.map_eq_some_iff, Sum.exists, Sum.elim_inl, negUnload, Sum.elim_inr,
      List.all_eq_true, decide_eq_true_eq, Prod.exists]
    intro f hf
    by_cases hp : f = ~(φ⋀ψ)
    · subst f
      right
      intro φ' ψ' _
      rcases hY with hY | hY <;> subst Y <;>
        simp <;> aesop
    · left
      rcases hf with hf | hf | hf | hf
      all_goals aesop
  case box α φ notAtom =>
    simp_all only [applyLocalRule, Finset.sdiff_empty, List.pdlToFinFin, Finset.mem_image,
      List.mem_toFinset, List.mem_map, exists_exists_and_eq_and, Finset.union_empty,
      Olf.change_old_none_none, Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
      Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
      negUnload, Sum.elim_inr, List.all_eq_true, decide_eq_true_eq, Prod.exists]
    intro f hf
    by_cases hp : f = ⌈α⌉φ
    · subst f
      right
      intro φ' ψ' α'
      refine ⟨by simp, by simp, by simp, ?_, by simp⟩
      intro heq
      injection heq with hα hφ
      subst α'; subst φ'
      simp only [unfoldBox, List.mem_map] at hY
      rcases hY with ⟨l, l_in, hY⟩
      rcases l_in with ⟨tp, tp_in, rfl⟩
      subst Y
      refine ⟨tp, ?_⟩
      intro x hx
      simp [hx]
    · left
      rcases hf with hf | hf | hf | hf
      all_goals aesop
  case dia α φ notAtom =>
    simp_all only [applyLocalRule, Finset.sdiff_empty, List.pdlToFinFin, Finset.mem_image,
      List.mem_toFinset, List.mem_map, exists_exists_and_eq_and, Finset.union_empty,
      Olf.change_old_none_none, Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
      Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
      negUnload, Sum.elim_inr, List.all_eq_true, decide_eq_true_eq, Prod.exists]
    intro f hf
    by_cases hp : f = ~⌈α⌉φ
    · subst f
      right
      intro φ' ψ' α'
      refine ⟨by simp, by simp, by simp, by simp, ?_⟩
      intro heq
      injection heq with hneg
      injection hneg with hα hφ
      subst α'; subst φ'
      simp only [unfoldDiamond, List.mem_map] at hY
      rcases hY with ⟨ys, ys_in, hY⟩
      rcases ys_in with ⟨Fδ, Fδ_in, rfl⟩
      subst Y
      rcases Fδ with ⟨Fs, δ⟩
      refine ⟨Fs, δ, Fδ_in, ?_⟩
      intro x hx
      simp [hx]
    · left
      rcases hf with hf | hf | hf | hf
      all_goals aesop
  all_goals simp_all [applyLocalRule]

/-- Preservation and expansion for a local rule acting on the R component. -/
private theorem formulaExpansion_oneSidedR
    {Y : Sequent} (L R : Finset Formula) (O : Olf) {Rcond : Finset Formula}
    {ress : Finset Sequent} {outputs : Finset (Finset Formula)}
    (orule : OneSidedLocalRule Rcond outputs) (pre : ∅ ⊆ L ∧ Rcond ⊆ R ∧ none ⊆ O)
    (YS_def : ress = outputs.image (fun res => (∅, res, none)))
    (hY : Y ∈ applyLocalRule (.oneSidedR orule YS_def) (L, R, O)) : ∀ f ∈ Sequent.toFinset (L, R,
      O),
      f ∈ Y.toFinset ∨
        (∀ (φ ψ : Formula) (α : Program),
          (f = (~~φ) → φ ∈ Y.toFinset) ∧
          (f = (φ⋀ψ) → φ ∈ Y.toFinset ∧ ψ ∈ Y.toFinset) ∧
          (f = (~(φ⋀ψ)) → (~φ) ∈ Y.toFinset ∨ (~ψ) ∈ Y.toFinset) ∧
          (f = (⌈α⌉φ) → ∃ l : TP α, (Bset α l φ).all (· ∈ Y.toFinset)) ∧
          (f = (~⌈α⌉φ) → ∃ Fδ ∈ Dset α, (Yset Fδ φ).all (· ∈ Y.toFinset))) := by
  subst YS_def
  cases orule
  case neg φ =>
    simp_all only [applyLocalRule, Finset.sdiff_empty, Finset.image_singleton,
      Finset.union_singleton, Finset.union_empty, Olf.change_old_none_none,
      Finset.mem_singleton, Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
      Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
      negUnload, Sum.elim_inr, Finset.insert_union, Finset.mem_insert, Finset.mem_sdiff,
      Formula.neg.injEq, List.all_eq_true, Prod.exists]
    intro f hf
    by_cases hp : f = ~~φ
    · subst f; right; simp
    · left
      rcases hf with hf | hf | hf | hf
      all_goals aesop
  case con φ ψ =>
    simp_all only [applyLocalRule, Finset.sdiff_empty, Finset.image_singleton,
      Finset.union_insert, Finset.union_singleton, Finset.union_empty, Olf.change_old_none_none,
      Finset.mem_singleton, Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
      Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
      negUnload, Sum.elim_inr, Finset.insert_union, Finset.mem_insert, Finset.mem_sdiff,
      reduceCtorEq, not_false_eq_true, and_true, Formula.neg.injEq, List.all_eq_true,
      Prod.exists]
    intro f hf
    by_cases hp : f = φ⋀ψ
    · subst f; right; simp
    · left
      rcases hf with hf | hf | hf | hf
      all_goals aesop
  case nCo φ ψ =>
    simp_all only [applyLocalRule, Finset.sdiff_empty, Finset.image_insert,
      Finset.image_singleton, Finset.union_singleton, Finset.union_empty,
      Olf.change_old_none_none, Finset.mem_insert, Finset.mem_singleton, Sequent.toFinset,
      Finset.union_assoc, Finset.mem_union, Option.mem_toFinset, Option.mem_def,
      Option.map_eq_some_iff, Sum.exists, Sum.elim_inl, negUnload, Sum.elim_inr,
      List.all_eq_true, decide_eq_true_eq, Prod.exists]
    intro f hf
    by_cases hp : f = ~(φ⋀ψ)
    · subst f
      right
      intro φ' ψ' _
      rcases hY with hY | hY <;> subst Y <;>
        simp <;> aesop
    · left
      rcases hf with hf | hf | hf | hf
      all_goals aesop
  case box α φ notAtom =>
    simp_all only [applyLocalRule, Finset.sdiff_empty, List.pdlToFinFin, Finset.mem_image,
      List.mem_toFinset, List.mem_map, exists_exists_and_eq_and, Finset.union_empty,
      Olf.change_old_none_none, Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
      Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
      negUnload, Sum.elim_inr, List.all_eq_true, decide_eq_true_eq, Prod.exists]
    intro f hf
    by_cases hp : f = ⌈α⌉φ
    · subst f
      right
      intro φ' ψ' α'
      refine ⟨by simp, by simp, by simp, ?_, by simp⟩
      intro heq
      injection heq with hα hφ
      subst α'; subst φ'
      simp only [unfoldBox, List.mem_map] at hY
      rcases hY with ⟨l, l_in, hY⟩
      rcases l_in with ⟨tp, tp_in, rfl⟩
      subst Y
      refine ⟨tp, ?_⟩
      intro x hx
      simp [hx]
    · left
      rcases hf with hf | hf | hf | hf
      all_goals aesop
  case dia α φ notAtom =>
    simp_all only [applyLocalRule, Finset.sdiff_empty, List.pdlToFinFin, Finset.mem_image,
      List.mem_toFinset, List.mem_map, exists_exists_and_eq_and, Finset.union_empty,
      Olf.change_old_none_none, Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
      Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
      negUnload, Sum.elim_inr, List.all_eq_true, decide_eq_true_eq, Prod.exists]
    intro f hf
    by_cases hp : f = ~⌈α⌉φ
    · subst f
      right
      intro φ' ψ' α'
      refine ⟨by simp, by simp, by simp, by simp, ?_⟩
      intro heq
      injection heq with hneg
      injection hneg with hα hφ
      subst α'; subst φ'
      simp only [unfoldDiamond, List.mem_map] at hY
      rcases hY with ⟨ys, ys_in, hY⟩
      rcases ys_in with ⟨Fδ, Fδ_in, rfl⟩
      subst Y
      rcases Fδ with ⟨Fs, δ⟩
      refine ⟨Fs, δ, Fδ_in, ?_⟩
      intro x hx
      simp [hx]
    · left
      rcases hf with hf | hf | hf | hf
      all_goals aesop
  all_goals simp_all [applyLocalRule]

/-- Preservation and expansion for a local rule acting on the L component. -/
private theorem formulaExpansion_loadedL
    {Y : Sequent} (L R : Finset Formula) (O : Olf) {ress : Finset Sequent}
    {outputs : Finset (Finset Formula × Option NegLoadFormula)}
    (χ : LoadFormula) (lrule : LoadRule (~'χ) outputs)
    (pre : ∅ ⊆ L ∧ ∅ ⊆ R ∧ some (Sum.inl (~'χ)) ⊆ O)
    (YS_def : ress = outputs.image (fun (X, o) => (X, ∅, o.map Sum.inl)))
    (hY : Y ∈ applyLocalRule (.loadedL χ lrule YS_def) (L, R, O)) : ∀ f ∈ Sequent.toFinset (L, R,
      O),
      f ∈ Y.toFinset ∨
        (∀ (φ ψ : Formula) (α : Program),
          (f = (~~φ) → φ ∈ Y.toFinset) ∧
          (f = (φ⋀ψ) → φ ∈ Y.toFinset ∧ ψ ∈ Y.toFinset) ∧
          (f = (~(φ⋀ψ)) → (~φ) ∈ Y.toFinset ∨ (~ψ) ∈ Y.toFinset) ∧
          (f = (⌈α⌉φ) → ∃ l : TP α, (Bset α l φ).all (· ∈ Y.toFinset)) ∧
          (f = (~⌈α⌉φ) → ∃ Fδ ∈ Dset α, (Yset Fδ φ).all (· ∈ Y.toFinset))) := by
  subst YS_def
  cases lrule
  case dia α χ notAtom =>
    simp_all only [applyLocalRule, Finset.sdiff_empty, List.pdlToFinFinOpt, Finset.mem_image,
      List.mem_toFinset, List.mem_map, Prod.exists, Prod.mk.injEq, exists_eq_right_right,
      ↓existsAndEq, and_true, Finset.union_empty, Sequent.toFinset, Finset.union_assoc,
      Finset.mem_union, Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists,
      Sum.elim_inl, negUnload, Sum.elim_inr, List.all_eq_true, decide_eq_true_eq]
    intro f hf
    by_cases hp : f = ~⌈α⌉χ.unload
    · subst f
      right
      intro φ ψ β
      refine ⟨by simp, by simp, by simp, by simp, ?_⟩
      intro heq
      injection heq with hn
      injection hn with hα hφ
      subst β; subst φ
      rcases hY with ⟨w, o, hwo, rfl⟩
      rcases loaded_unfold_child_closes_left hwo with ⟨⟨Fs,δ⟩, hD, hclose⟩
      refine ⟨Fs, δ, hD, ?_⟩
      obtain ⟨-, -, hO⟩ := pre
      rw [Option.some_subseteq] at hO
      cases hO
      intro x hx
      rcases hclose x hx with h | h
      · simp only [Finset.mem_union, List.mem_toFinset]
        tauto
      · rcases w with _ | nlf <;> simp_all [Olf.L]
    · left; aesop
  case dia' α φ notAtom =>
    simp_all only [applyLocalRule, Finset.sdiff_empty, List.pdlToFinFinOpt, Finset.mem_image,
      List.mem_toFinset, List.mem_map, Prod.exists, Prod.mk.injEq, exists_eq_right_right,
      ↓existsAndEq, and_true, Finset.union_empty, Sequent.toFinset, Finset.union_assoc,
      Finset.mem_union, Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists,
      Sum.elim_inl, negUnload, Sum.elim_inr, List.all_eq_true, decide_eq_true_eq]
    intro f hf
    by_cases hp : f = ~⌈α⌉φ
    · subst f
      right
      intro φ' ψ β
      refine ⟨by simp, by simp, by simp, by simp, ?_⟩
      intro heq
      injection heq with hn
      injection hn with hα hφ
      subst β; subst φ'
      rcases hY with ⟨w, o, hwo, rfl⟩
      rcases loaded_unfold'_child_closes_left hwo with ⟨⟨Fs,δ⟩, hD, hclose⟩
      refine ⟨Fs, δ, hD, ?_⟩
      obtain ⟨-, -, hO⟩ := pre
      rw [Option.some_subseteq] at hO
      cases hO
      intro x hx
      rcases hclose x hx with h | h
      · simp only [Finset.mem_union, List.mem_toFinset]
        tauto
      · rcases w with _ | nlf <;> simp_all [Olf.L]
    · left; aesop

/-- Preservation and expansion for a local rule acting on the R component. -/
private theorem formulaExpansion_loadedR
    {Y : Sequent} (L R : Finset Formula) (O : Olf) {ress : Finset Sequent}
    {outputs : Finset (Finset Formula × Option NegLoadFormula)}
    (χ : LoadFormula) (lrule : LoadRule (~'χ) outputs)
    (pre : ∅ ⊆ L ∧ ∅ ⊆ R ∧ some (Sum.inr (~'χ)) ⊆ O)
    (YS_def : ress = outputs.image (fun (X, o) => (∅, X, o.map Sum.inr)))
    (hY : Y ∈ applyLocalRule (.loadedR χ lrule YS_def) (L, R, O)) : ∀ f ∈ Sequent.toFinset (L, R,
      O),
      f ∈ Y.toFinset ∨
        (∀ (φ ψ : Formula) (α : Program),
          (f = (~~φ) → φ ∈ Y.toFinset) ∧
          (f = (φ⋀ψ) → φ ∈ Y.toFinset ∧ ψ ∈ Y.toFinset) ∧
          (f = (~(φ⋀ψ)) → (~φ) ∈ Y.toFinset ∨ (~ψ) ∈ Y.toFinset) ∧
          (f = (⌈α⌉φ) → ∃ l : TP α, (Bset α l φ).all (· ∈ Y.toFinset)) ∧
          (f = (~⌈α⌉φ) → ∃ Fδ ∈ Dset α, (Yset Fδ φ).all (· ∈ Y.toFinset))) := by
  subst YS_def
  cases lrule
  case dia α χ notAtom =>
    simp_all only [applyLocalRule, Finset.sdiff_empty, List.pdlToFinFinOpt, Finset.mem_image,
      List.mem_toFinset, List.mem_map, Prod.exists, Prod.mk.injEq, exists_eq_right_right,
      ↓existsAndEq, and_true, Finset.union_empty, Sequent.toFinset, Finset.union_assoc,
      Finset.mem_union, Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists,
      Sum.elim_inl, negUnload, Sum.elim_inr, List.all_eq_true, decide_eq_true_eq]
    intro f hf
    by_cases hp : f = ~⌈α⌉χ.unload
    · subst f
      right
      intro φ ψ β
      refine ⟨by simp, by simp, by simp, by simp, ?_⟩
      intro heq
      injection heq with hn
      injection hn with hα hφ
      subst β; subst φ
      rcases hY with ⟨w, o, hwo, rfl⟩
      rcases loaded_unfold_child_closes_right hwo with ⟨⟨Fs,δ⟩, hD, hclose⟩
      refine ⟨Fs, δ, hD, ?_⟩
      obtain ⟨-, -, hO⟩ := pre
      rw [Option.some_subseteq] at hO
      cases hO
      intro x hx
      rcases hclose x hx with h | h
      · simp only [Finset.mem_union, List.mem_toFinset]
        tauto
      · rcases w with _ | nlf <;> simp_all [Olf.R]
    · left; aesop
  case dia' α φ notAtom =>
    simp_all only [applyLocalRule, Finset.sdiff_empty, List.pdlToFinFinOpt, Finset.mem_image,
      List.mem_toFinset, List.mem_map, Prod.exists, Prod.mk.injEq, exists_eq_right_right,
      ↓existsAndEq, and_true, Finset.union_empty, Sequent.toFinset, Finset.union_assoc,
      Finset.mem_union, Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists,
      Sum.elim_inl, negUnload, Sum.elim_inr, List.all_eq_true, decide_eq_true_eq]
    intro f hf
    by_cases hp : f = ~⌈α⌉φ
    · subst f
      right
      intro φ' ψ β
      refine ⟨by simp, by simp, by simp, by simp, ?_⟩
      intro heq
      injection heq with hn
      injection hn with hα hφ
      subst β; subst φ'
      rcases hY with ⟨w, o, hwo, rfl⟩
      rcases loaded_unfold'_child_closes_right hwo with ⟨⟨Fs,δ⟩, hD, hclose⟩
      refine ⟨Fs, δ, hD, ?_⟩
      obtain ⟨-, -, hO⟩ := pre
      rw [Option.some_subseteq] at hO
      cases hO
      intro x hx
      rcases hclose x hx with h | h
      · simp only [Finset.mem_union, List.mem_toFinset]
        tauto
      · rcases w with _ | nlf <;> simp_all [Olf.R]
    · left; aesop

/-- Every formula at the source of a local rule is retained by the chosen child or has
its principal-formula expansion in that child. -/
lemma LocalRuleApp.formula_preserved_or_expanded (lra : LocalRuleApp) {Y : Sequent}
    (hY : Y ∈ lra.C) : ∀ f ∈ lra.X.toFinset,
      f ∈ Y.toFinset ∨
        (∀ (φ ψ : Formula) (α : Program),
          (f = (~~φ) → φ ∈ Y.toFinset) ∧
          (f = (φ⋀ψ) → φ ∈ Y.toFinset ∧ ψ ∈ Y.toFinset) ∧
          (f = (~(φ⋀ψ)) → (~φ) ∈ Y.toFinset ∨ (~ψ) ∈ Y.toFinset) ∧
          (f = (⌈α⌉φ) → ∃ l : TP α, (Bset α l φ).all (· ∈ Y.toFinset)) ∧
          (f = (~⌈α⌉φ) → ∃ Fδ ∈ Dset α, (Yset Fδ φ).all (· ∈ Y.toFinset))) := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  subst C
  cases rule
  case oneSidedL orule YS_def =>
    exact formulaExpansion_oneSidedL L R O orule pre YS_def hY
  case oneSidedR orule YS_def =>
    exact formulaExpansion_oneSidedR L R O orule pre YS_def hY
  case loadedL χ lrule YS_def =>
    exact formulaExpansion_loadedL L R O χ lrule pre YS_def hY
  case loadedR χ lrule YS_def =>
    exact formulaExpansion_loadedR L R O χ lrule pre YS_def hY
  all_goals simp_all [applyLocalRule]

/-! # Saturated and Locally Consistent Sets of Formulas -/

/-- A set of formulas is *saturated* if it is closed under:
removing double negations, splitting (negated) conjunctions,
unfolding boxes using any test profile, and unfolding diamonds using `H`.
Part of Def 6.2 -/
@[expose] def saturated : Finset Formula → Prop
  | X => ∀ (φ ψ : Formula) (α : Program),
    -- propositional closure:
      ((~~φ) ∈ X → φ ∈ X)
    ∧ (φ⋀ψ ∈ X → φ ∈ X ∧ ψ ∈ X)
    ∧ ((~(φ⋀ψ)) ∈ X → (~φ) ∈ X ∨ (~ψ) ∈ X)
    -- programs closure, now only two general cases, no program subcases:
    ∧ ((⌈α⌉φ) ∈ X → ∃ l : TP α, (Bset α l φ).all (fun y => y ∈ X))
    ∧ ((~⌈α⌉φ) ∈ X → ∃ Fδ ∈ Dset α, (Yset Fδ φ).all (fun y => y ∈ X))

/-- Any basic sequent is also saturated. -/
lemma Sequent.basic_then_saturated {X : Sequent} : X.basic → saturated X.toFinset := by
  intro Xbas
  rcases X with ⟨L,R,O⟩
  unfold saturated
  intro Fs φ ψ α
  refine ⟨?_, ?_, ?_, ?box, ?dia⟩
  · simp_all [basic, Fs, toFinset]
    grind
  · simp_all [basic, Fs, toFinset]
    grind
  · simp_all [basic, Fs, toFinset]
    grind
  case box =>
    intro _in_F
    simp_all only [basic, toFinset, Finset.union_assoc, Finset.mem_union, Option.mem_toFinset,
      Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl, negUnload, Sum.elim_inr,
      Formula.basic, decide_false, decide_true, reduceCtorEq, and_false, exists_false, or_self,
      or_false, List.all_eq_true, Fs]
    cases α
    case atom_prog =>
      simp only [TP, testsOfProgram, Bset, F, List.empty_eq, P, List.map_cons, Formula.boxes_cons,
        Formula.boxes_nil, List.map_nil, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false, Finset.union_assoc, Finset.mem_union, Option.mem_toFinset, Option.mem_def,
        Option.map_eq_some_iff, Sum.exists, Sum.elim_inl, negUnload, Sum.elim_inr, forall_eq,
        reduceCtorEq, and_false, exists_false, or_self, Bool.decide_or, Bool.or_eq_true,
        decide_eq_true_eq, exists_const]
      exact _in_F
    all_goals
      simp [TP, testsOfProgram,Bset,P,F]
      grind
  case dia =>
    intro _in_F
    cases α
    case atom_prog =>
      -- Note: we must not unfold `Fs` here, because since Lean 4.33 that would leave the
      -- `Decidable` instance inside `decide` mentioning `Fs`, blocking `decide_eq_true_eq`.
      simp only [Dset, List.mem_cons, List.not_mem_nil, or_false, Yset, List.all_eq_true,
        List.mem_union_iff, decide_eq_true_eq, exists_eq_left, Formula.boxes_cons,
        Formula.boxes_nil, false_or, forall_eq]
      exact _in_F
    all_goals
      simp_all [basic, Fs, toFinset]
      simp [Dset, Yset]
      grind

/-- A set of formulas is *lcoally consistent* iff it does not contain `⊥`
and for all atoms `p ∈ X` we do not have `~p ∈ X`. Part of Def 6.2 -/
@[expose] def locallyConsistent (X : Finset Formula) : Prop :=
  ⊥ ∉ X.val ∧ ∀ pp, (·pp : Formula) ∈ X.val → (~(·pp)) ∉ X.val

lemma Sequent.basic_to_locallyConsistent {X : Sequent} (bas : X.basic) :
    locallyConsistent X.toFinset := by
  rcases X with ⟨L, R, O⟩
  unfold locallyConsistent Sequent.toFinset at *
  constructor
  · intro hbot
    apply bas.2
    unfold Sequent.closed
    left
    simp_all
  · intro p hp hnp
    apply bas.2
    unfold Sequent.closed
    right
    refine ⟨(·p), ?_, ?_⟩
    · simp_all
    · simp_all only [Finset.union_assoc, Finset.union_val, Multiset.mem_union, Finset.mem_val,
      Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
      negUnload, reduceCtorEq, and_false, exists_false, Sum.elim_inr, or_self, or_false,
      Formula.neg.injEq, mem_def, L_eq, R_eq]
      rcases hnp with h | h | ⟨a, rfl, ha⟩ | ⟨b, rfl, hb⟩
      · exact Or.inl h
      · exact Or.inr h
      · rcases a with ⟨⟨α, af⟩⟩
        cases af <;> simp [LoadFormula.unload] at ha
      · rcases b with ⟨⟨α, af⟩⟩
        cases af <;> simp [LoadFormula.unload] at hb


-- TODO golf/shorten this
/-- LocalRuleApp preserves saturatedness backwards. -/
lemma LocalRuleApp.preserve_saturated_up (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, ∀ (rest : Finset Sequent) ,
      Y ∈ rest →
      saturated ((rest.image Sequent.toFinset).sup id)
        → saturated ((({lra.X} ∪ rest).image Sequent.toFinset).sup id) := by
  intro Y hY rest hYr hs
  simp only [saturated] at hs ⊢
  intro φ ψ α
  have old_or_rest (f : Formula) :
      f ∈ (({lra.X} ∪ rest).image Sequent.toFinset).sup id →
      f ∈ lra.X.toFinset ∨ f ∈ (rest.image Sequent.toFinset).sup id := by simp
  have child_in_rest (f : Formula) (hf : f ∈ Y.toFinset) :
      f ∈ (rest.image Sequent.toFinset).sup id := by simp; grind
  have lift_rest (f : Formula) :
      f ∈ (rest.image Sequent.toFinset).sup id →
      f ∈ (({lra.X} ∪ rest).image Sequent.toFinset).sup id := by simp_all
  have source_closure := lra.formula_preserved_or_expanded hY
  rcases hs φ ψ α with ⟨hneg, hcon, hncon, hbox, hdia⟩
  constructor
  · intro h
    rcases old_or_rest _ h with hsrc | hrest
    · rcases source_closure _ hsrc with hkeep | hexpand
      · exact lift_rest _ (hneg (child_in_rest _ hkeep))
      · exact lift_rest _ (child_in_rest _ ((hexpand φ ψ α).1 rfl))
    · exact lift_rest _ (hneg hrest)
  constructor
  · intro h
    rcases old_or_rest _ h with hsrc | hrest
    · rcases source_closure _ hsrc with hkeep | hexpand
      · rcases hcon (child_in_rest _ hkeep) with ⟨hφ, hψ⟩
        exact ⟨lift_rest _ hφ, lift_rest _ hψ⟩
      · rcases (hexpand φ ψ α).2.1 rfl with ⟨hφ, hψ⟩
        exact ⟨lift_rest _ (child_in_rest _ hφ), lift_rest _ (child_in_rest _ hψ)⟩
    · rcases hcon hrest with ⟨hφ, hψ⟩
      exact ⟨lift_rest _ hφ, lift_rest _ hψ⟩
  constructor
  · intro h
    rcases old_or_rest _ h with hsrc | hrest
    · rcases source_closure _ hsrc with hkeep | hexpand
      · exact (hncon (child_in_rest _ hkeep)).imp (lift_rest _) (lift_rest _)
      · rcases (hexpand φ ψ α).2.2.1 rfl with hφ | hψ
        · exact Or.inl (lift_rest _ (child_in_rest _ hφ))
        · exact Or.inr (lift_rest _ (child_in_rest _ hψ))
    · exact (hncon hrest).imp (lift_rest _) (lift_rest _)
  constructor
  · intro h
    rcases old_or_rest _ h with hsrc | hrest
    · rcases source_closure _ hsrc with hkeep | hexpand
      · rcases hbox (child_in_rest _ hkeep) with ⟨l, hl⟩
        simp only [List.all_eq_true, decide_eq_true_eq] at hl
        exact ⟨l, by simpa using fun f hf => lift_rest _ (by simpa using hl f hf)⟩
      · rcases (hexpand φ ψ α).2.2.2.1 rfl with ⟨l, hl⟩
        simp only [List.all_eq_true, decide_eq_true_eq] at hl
        exact ⟨l, by simpa using fun f hf => lift_rest _ (child_in_rest _ (by simpa using hl f hf))⟩
    · rcases hbox hrest with ⟨l, hl⟩
      simp only [List.all_eq_true, decide_eq_true_eq] at hl
      exact ⟨l, by simpa using fun f hf => lift_rest _ (by simpa using hl f hf)⟩
  · intro h
    rcases old_or_rest _ h with hsrc | hrest
    · rcases source_closure _ hsrc with hkeep | hexpand
      · rcases hdia (child_in_rest _ hkeep) with ⟨Fδ, hD, hF⟩
        simp only [List.all_eq_true, decide_eq_true_eq] at hF
        exact ⟨Fδ, hD, by simpa using fun f hf => lift_rest _ (by simpa using hF f hf)⟩
      · rcases (hexpand φ ψ α).2.2.2.2 rfl with ⟨Fδ, hD, hF⟩
        simp only [List.all_eq_true, decide_eq_true_eq] at hF
        exact ⟨ Fδ, hD
              , by simpa using fun f hf => lift_rest _ (child_in_rest _ (by simpa using hF f hf))⟩
    · rcases hdia hrest with ⟨Fδ, hD, hF⟩
      simp only [List.all_eq_true, decide_eq_true_eq] at hF
      exact ⟨Fδ, hD, by simpa using fun f hf => lift_rest _ (by simpa using hF f hf)⟩

/-- A free diamond at the source of a local rule application is either kept in the chosen child,
or it is the principal formula, and then the child contains one of its unfoldings.
Analogous to `LocalRuleApp.formula_preserved_or_expanded`, but for `Sequent.wForms`, i.e. here
we also know that the formulas in the child occur *unloaded*. (This is why we cannot obtain this
lemma from `LocalRuleApp.formula_preserved_or_expanded`: the latter uses `Sequent.toFinset`,
where a formula may also come from *unloading* the loaded formula of a sequent.) -/
lemma LocalRuleApp.wForms_negBox_preserved_or_unfolded (lra : LocalRuleApp) {Y : Sequent}
    (hY : Y ∈ lra.C) {α φ} (h : (~⌈α⌉φ : WhateverFormula) ∈ lra.X.wForms) :
    ((~⌈α⌉φ : WhateverFormula) ∈ Y.wForms)
    ∨ ∃ Fδ ∈ Dset α, (Yset Fδ φ).all (fun f => (f : WhateverFormula) ∈ Y.wForms) := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  subst hC
  simp only [LocalRuleApp.X] at h
  rw [Sequent.mem_wForms_normal_iff] at h
  simp only [applyLocalRule, Finset.mem_image] at hY
  rcases hY with ⟨⟨Lnew, Rnew, Onew⟩, res_in, rfl⟩
  by_cases hcond : (~⌈α⌉φ) ∈ Lcond ∨ (~⌈α⌉φ) ∈ Rcond
  · -- The diamond is the principal formula, so the only possible rule is its unfolding.
    right
    cases rule with
    | oneSidedL orule ress_def =>
      cases orule <;> simp_all only [Finset.image_empty, Finset.notMem_empty,
        Finset.image_singleton, Finset.mem_singleton, Formula.neg.injEq, reduceCtorEq, or_self,
        Finset.image_insert, Finset.mem_insert, List.pdlToFinFin, Finset.mem_image,
        List.mem_toFinset, List.mem_map, exists_exists_and_eq_and, Formula.box.injEq, or_false,
        Finset.singleton_subset_iff, Finset.empty_subset, Option.none_subseteq, and_self,
        and_true, Finset.sdiff_empty, Function.comp_apply, List.all_eq_true, decide_eq_true_eq,
        Prod.exists, true_or]
      rcases res_in with ⟨a, a_in, ha⟩
      simp only [unfoldDiamond, List.mem_map] at a_in
      rcases a_in with ⟨⟨F, δ⟩, Fδ_in, rfl⟩
      cases ha
      refine ⟨F, δ, Fδ_in, fun x hx => Sequent.mem_wForms_normal_iff.mpr ?_⟩
      simp
      grind
    | oneSidedR orule ress_def =>
      cases orule <;> simp_all only [Finset.image_empty, Finset.notMem_empty,
        Finset.image_singleton, Finset.mem_singleton, Formula.neg.injEq, reduceCtorEq, or_self,
        Finset.image_insert, Finset.mem_insert, List.pdlToFinFin, Finset.mem_image,
        List.mem_toFinset, List.mem_map, exists_exists_and_eq_and, Formula.box.injEq, false_or,
        Finset.empty_subset, Finset.singleton_subset_iff, Option.none_subseteq, and_true,
        true_and, Finset.sdiff_empty, Function.comp_apply, List.all_eq_true, decide_eq_true_eq,
        Prod.exists, or_true]
      rcases res_in with ⟨a, a_in, ha⟩
      simp only [unfoldDiamond, List.mem_map] at a_in
      rcases a_in with ⟨⟨F, δ⟩, Fδ_in, rfl⟩
      cases ha
      refine ⟨F, δ, Fδ_in, fun x hx => Sequent.mem_wForms_normal_iff.mpr ?_⟩
      simp
      grind
    | _ => simp_all
  · -- The diamond is not the principal formula, so it is kept in the chosen child.
    left
    push Not at hcond
    rw [Sequent.mem_wForms_normal_iff]
    rcases h with hL | hR <;> grind

/-- A loaded diamond at the source of a local rule application is either kept in the chosen child,
or it is the principal formula, and then the child contains one of the results of the `LoadRule`
that was applied to it.
This is the loaded analogue of `LocalRuleApp.wForms_negBox_preserved_or_unfolded`. -/
lemma LocalRuleApp.wForms_negLoad_preserved_or_unfolded (lra : LocalRuleApp) {Y : Sequent}
    (hY : Y ∈ lra.C) {nlf : NegLoadFormula}
    (h : (WhateverFormula.negLoad nlf) ∈ lra.X.wForms) :
    ((WhateverFormula.negLoad nlf) ∈ Y.wForms)
    ∨ ∃ ress, Nonempty (LoadRule nlf ress) ∧ ∃ Fo ∈ ress,
        Fo.1.sort.all (fun f => (f : WhateverFormula) ∈ Y.wForms)
        ∧ Fo.2.toList.all (fun nl => (WhateverFormula.negLoad nl) ∈ Y.wForms) := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  subst hC
  simp only [LocalRuleApp.X] at h
  rw [Sequent.mem_wForms_negLoad_iff] at h
  cases rule
  case oneSidedL ress' orule ress_def | oneSidedR ress' orule ress_def =>
    -- One-sided rules do not change the loaded formula, so it is kept.
    subst ress_def
    simp only [applyLocalRule, Finset.sdiff_empty, Finset.mem_image, exists_exists_and_eq_and,
      Finset.union_empty, Olf.change_old_none_none] at hY
    rcases hY with ⟨res, res_in, rfl⟩
    left
    rw [Sequent.mem_wForms_negLoad_iff]
    simpa using h
  case LRnegL ψ => simp at hY
  case LRnegR ψ => simp at hY
  case loadedL ress' χ lrule ress_def =>
    subst ress_def
    simp only [applyLocalRule, Finset.sdiff_empty, Finset.mem_image, Prod.exists, ↓existsAndEq,
      and_true, Finset.union_empty] at hY
    rcases hY with ⟨Xnew, onew, res_in, rfl⟩
    right
    have nlf_def : nlf = ~'χ := by
      rcases pre with ⟨_, _, hO⟩
      rcases h with hO' | hO' <;> rw [hO'] at hO <;> simp_all
    subst nlf_def
    refine ⟨ress', ⟨lrule⟩, ⟨Xnew, onew⟩, res_in, ?_, ?_⟩
    · simp only [List.all_eq_true, decide_eq_true_eq]
      intro f f_in
      rw [Sequent.mem_wForms_normal_iff]
      aesop
    · cases onew with
      | none => simp
      | some nl =>
        simp only [Option.toList_some, List.all_cons, List.all_nil, Bool.and_true,
          decide_eq_true_eq]
        rw [Sequent.mem_wForms_negLoad_iff]
        simp
  case loadedR ress' χ lrule ress_def =>
    subst ress_def
    simp only [applyLocalRule, Finset.sdiff_empty, Finset.mem_image, Prod.exists, ↓existsAndEq,
      and_true, Finset.union_empty] at hY
    rcases hY with ⟨Xnew, onew, res_in, rfl⟩
    right
    have nlf_def : nlf = ~'χ := by
      rcases pre with ⟨_, _, hO⟩
      rcases h with hO' | hO' <;> rw [hO'] at hO <;> simp_all
    subst nlf_def
    refine ⟨ress', ⟨lrule⟩, ⟨Xnew, onew⟩, res_in, ?_, ?_⟩
    · simp only [List.all_eq_true, decide_eq_true_eq]
      intro f f_in
      rw [Sequent.mem_wForms_normal_iff]
      aesop
    · cases onew with
      | none => simp
      | some nl =>
        simp only [Option.toList_some, List.all_cons, List.all_nil, Bool.and_true,
          decide_eq_true_eq]
        rw [Sequent.mem_wForms_negLoad_iff]
        simp

/-- The only `LoadRule` applicable to `~'⌊α⌋χ` for a loaded `χ` is `LoadRule.dia`. -/
lemma LoadRule.eq_unfoldDiamondLoaded {α} {χ : LoadFormula} {ress}
    (lr : LoadRule (~'⌊α⌋(AnyFormula.loaded χ)) ress) :
    ress = (unfoldDiamondLoaded α χ).pdlToFinFinOpt := by
  cases lr; rfl

/-- The only `LoadRule` applicable to `~'⌊α⌋φ` for a normal `φ` is `LoadRule.dia'`. -/
lemma LoadRule.eq_unfoldDiamondLoaded' {α} {φ : Formula} {ress}
    (lr : LoadRule (~'⌊α⌋(AnyFormula.normal φ)) ress) :
    ress = (unfoldDiamondLoaded' α φ).pdlToFinFinOpt := by
  cases lr; rfl

-- case distinction over all local rules, with heavy `simp_all` and `grind` calls in each case
/-- Local rule applications preserve *basic* formulas: no local rule with children can have
a basic formula as its principal formula.
Note that `⊥` is not basic, for that case see `LocalRuleApp.preserve_bottom_down`. -/
lemma LocalRuleApp.preserve_basic_down (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, ∀ f, f.basic → f ∈ lra.X.toFinset → f ∈ Y.toFinset := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  subst hC
  cases rule <;> simp_all only [applyLocalRule, Finset.sdiff_empty, Finset.mem_image,
    exists_exists_and_eq_and, Finset.union_empty, Olf.change_old_none_none, Formula.basic,
    decide_false, decide_true, Sequent.toFinset, Finset.union_assoc, Finset.mem_union,
    Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl,
    negUnload, Sum.elim_inr, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Finset.mem_sdiff, Finset.image_empty, Finset.notMem_empty, implies_true, forall_const,
    not_isEmpty_of_nonempty, IsEmpty.forall_iff, Prod.exists, ↓existsAndEq, and_true]
  case oneSidedL ress orule ress_def => cases orule <;> simp_all <;> grind [Program.isAtomic]
  case oneSidedR ress orule ress_def => cases orule <;> simp_all <;> grind [Program.isAtomic]
  case loadedL ress chi lrule ress_def =>
    cases lrule <;> simp_all only [Finset.empty_subset, Option.some_subseteq, true_and,
      List.pdlToFinFinOpt, List.mem_toFinset, List.mem_map, Prod.mk.injEq, Prod.exists,
      exists_eq_right_right, forall_exists_index, and_imp] <;> intros <;> subst_eqs <;> simp_all
        <;> grind [Program.isAtomic]
  case loadedR ress chi lrule ress_def =>
    cases lrule <;> simp_all only [Finset.empty_subset, Option.some_subseteq, true_and,
      List.pdlToFinFinOpt, List.mem_toFinset, List.mem_map, Prod.mk.injEq, Prod.exists,
      exists_eq_right_right, forall_exists_index, and_imp] <;> intros <;> subst_eqs <;> simp_all
        <;> grind [Program.isAtomic]

/-- Local rules never *load* a formula: if the sequent we apply a local rule to is free,
then so are all children. (The rules `loadedL` and `loadedR` are not applicable to a free
sequent, and all other local rules leave the `Olf` component unchanged.) -/
lemma LocalRuleApp.preserve_free (lra : LocalRuleApp) (hfree : lra.O = none) :
    ∀ Y ∈ lra.C, Y.O = none := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  simp only at hfree
  subst hfree
  subst hC
  cases rule
  case oneSidedL ress orule ress_def => subst ress_def; rintro Y hY; simp at hY; grind [Sequent.O]
  case oneSidedR ress orule ress_def => subst ress_def; rintro Y hY; simp at hY; grind [Sequent.O]
  case LRnegL => simp_all
  case LRnegR => simp_all
  case loadedL => exact absurd pre.2.2 (by simp)
  case loadedR => exact absurd pre.2.2 (by simp)

end PDL
