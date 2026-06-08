/-
Copyright (c) 2026 Paul Mure, Joonhyup Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure, Joonhyup Lee
-/
import Lean.Meta
import Lean.Elab

namespace Lean.Order.CompleteLattice

open PartialOrder
-- The meet (`⊓ₚ`) and top (`⊤ₚ`) notations and the `meet_le_*` helper lemmas
-- below use the `ₚ`/`'` suffix to avoid clashing with the `Lean.Order` complete
-- lattice operations (`⊓`, `⊤`, `meet_le_left`, `meet_le_right`) that Lean core
-- introduced (via `Std.Internal.Do.Assertion`) and which are now in scope here.
/-- The binary meet of a complete lattice, as the infimum of `{x, y}`. -/
noncomputable instance instMinCompleteLattice [CompleteLattice α] : Min α where
  min x y := inf (λ z => z = x ∨ z = y)

/-- The top element of a complete lattice, as the supremum of the whole carrier. -/
noncomputable def top [CompleteLattice α] : α := sup (λ _ => True)

/-- Notation `⊤ₚ` for the Paco lattice top (to avoid clashing with core's `⊤`). -/
scoped notation "⊤ₚ" => top
/-- Notation `x ⊓ₚ y` for the Paco lattice meet (to avoid clashing with core's `⊓`). -/
scoped infixl:60 " ⊓ₚ " => min

theorem top_spec [CompleteLattice α] (x : α) : x ⊑ ⊤ₚ := le_sup _ True.intro

theorem meet_spec [CompleteLattice α] (x y : α) : z ⊑ x ⊓ₚ y ↔ z ⊑ x ∧ z ⊑ y := by
  constructor <;> simp only [min, inf_spec]
  · exact λ h => ⟨h _ <| Or.intro_left _ rfl, h _ <| Or.intro_right _ rfl⟩
  · intro ⟨hx, hy⟩
    intros; rename_i h
    cases h <;> (rename_i h; subst h; assumption)

theorem meet_le_left' [CompleteLattice α] (x : α) : x ⊑ z → x ⊓ₚ y ⊑ z := by
  simp only [min]
  intros
  apply rel_trans _ (by assumption)
  apply sup_le
  intros; rename_i h; apply h; left; rfl

theorem meet_le_right' [CompleteLattice α] (y : α) : y ⊑ z → x ⊓ₚ y ⊑ z := by
  simp only [min]
  intros
  apply rel_trans _ (by assumption)
  apply sup_le
  intros; rename_i h; apply h; right; rfl

theorem meet_top [CompleteLattice α] (x : α) : x ⊓ₚ ⊤ₚ = x :=
  rel_antisymm (meet_le_left' _ rel_refl) <| (meet_spec x ⊤ₚ).mpr ⟨rel_refl, top_spec _⟩

theorem meet_comm [CompleteLattice α] (x y : α) : x ⊓ₚ y = y ⊓ₚ x :=
  rel_antisymm
    ((meet_spec _ _).mpr ⟨meet_le_right' _ rel_refl, meet_le_left' _ rel_refl⟩)
    ((meet_spec _ _).mpr ⟨meet_le_right' _ rel_refl, meet_le_left' _ rel_refl⟩)

theorem meet_assoc [CompleteLattice α] (x y z : α) : x ⊓ₚ y ⊓ₚ z = x ⊓ₚ (y ⊓ₚ z) := by
  apply rel_antisymm <;> (rw [meet_spec]; apply And.intro)
  · apply meet_le_left'; apply meet_le_left'; apply rel_refl
  · rw [meet_spec]; apply And.intro
    · apply meet_le_left'; apply meet_le_right'; apply rel_refl
    · apply meet_le_right'; apply rel_refl
  · rw [meet_spec]; apply And.intro
    · apply meet_le_left'; apply rel_refl
    · apply meet_le_right'; apply meet_le_left'; apply rel_refl
  · apply meet_le_right'; apply meet_le_right'; apply rel_refl

end Lean.Order.CompleteLattice

namespace Lean4Itree

open Lean.Order PartialOrder CompleteLattice

-- note that we don't require monotonicity for f
-- this is the version in paco
theorem monotonize_mon [Lean.Order.CompleteLattice α] (f : α → α) (r : α) :
  monotone (λ x => inf (λ z => ∃ y, z = f y ∧ r ⊓ₚ x ⊑ y)) := by
  simp only [monotone]
  intros _ _ h
  apply le_sup; intro z ⟨y, heq, h'⟩
  subst heq
  apply Lean.Order.sup_le; intro _ le
  apply le
  exists y; apply And.intro rfl
  apply rel_trans _ h'
  rw [meet_spec]
  apply And.intro
  · apply meet_le_left' _ rel_refl
  · apply meet_le_right' _ h

theorem plfp_arg_mon [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) (r : α) :
  monotone (λ x => f (r ⊓ₚ x)) := by
  simp only [monotone]
  intros
  apply hm
  rw [meet_spec]
  apply And.intro
  · apply meet_le_left'; apply rel_refl
  · apply meet_le_right'; assumption

/--
Parameterized least fixed point, we don't "monotonize" f (⌈f⌉) as in paco for now
version in paco: lfp (λ x => inf (λ z => ∃ y, z = f y ∧ r ⊓ₚ x ⊑ y)
-/
noncomputable def plfp [Lean.Order.CompleteLattice α] (f : α → α) {hm : monotone f} (r : α) :=
  lfp_monotone (λ x => f (r ⊓ₚ x)) (plfp_arg_mon hm r)

/-- The "unfolded" parameterized least fixed point `r ⊓ₚ plfp f r`. -/
noncomputable def uplfp [Lean.Order.CompleteLattice α] (f : α → α) {hm : monotone f} (r : α) :=
  r ⊓ₚ (plfp f (hm := hm) r)

theorem plfp_mon [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) :
  monotone (plfp f (hm := hm)) := by
  simp only [monotone, plfp]
  intros
  apply le_sup; intros; apply Lean.Order.sup_le; intros
  rename_i h; apply h
  rename_i h' _; apply rel_trans _ h'; simp only; apply hm
  rw [meet_spec]; apply And.intro
  · apply rel_trans _ (by assumption)
    apply meet_le_left'; apply rel_refl
  · apply meet_le_right'; apply rel_refl

theorem plfp_init [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) :
  lfp_monotone f hm = plfp f (hm := hm) ⊤ₚ := by
  apply rel_antisymm <;>
  (apply le_sup; intros; apply Lean.Order.sup_le; intros; rename_i h; apply h) <;>
  (rename_i h' _; apply rel_trans _ h'; simp only) <;>
  (rw [meet_comm, meet_top] <;> apply rel_refl)

theorem plfp_unfold [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) :
  plfp f (hm := hm) r = f (uplfp f (hm := hm) r) := by
  rw [plfp]
  delta lfp_monotone
  have h := plfp_arg_mon hm r
  rw [lfp_fix h]
  congr

theorem uplfp_goal [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) :
  r ⊑ z ∨ plfp f (hm := hm) r ⊑ z → uplfp (hm := hm) f r ⊑ z := by
  simp only [uplfp]
  intro h; cases h
  · apply meet_le_left'; assumption
  · apply meet_le_right'; assumption

theorem uplfp_hyp [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) :
  z ⊑ uplfp (hm := hm) f r → z ⊑ r ∧ z ⊑ plfp f (hm := hm) r := by
  simp only [uplfp]
  rw [meet_spec]
  exact id

theorem fun_sup_equiv {α : Sort u} {β : α → Sort v} [(x : α) → CompleteLattice (β x)]
  (c : ((x : α) → β x) → Prop) (x : α) :
  fun_sup c x = inf λ y => ∀ f, c f → f x ⊑ y := by
  rw [inf, fun_sup]
  apply rel_antisymm
  · apply sup_le; intro y ⟨f, inc, eqf⟩
    subst eqf
    apply le_sup
    intros; rename_i h; apply h _ inc
  · rw [sup_spec]
    intros
    rename_i h
    apply h
    intros
    apply le_sup; rename_i f _; exists f

theorem plfp_acc_aux [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) (r x : α) :
  plfp f (hm := hm) r ⊑ x ↔ plfp f (hm := hm) (r ⊓ₚ x) ⊑ x := by
  constructor <;> (intro h; apply rel_trans _ h)
  · apply plfp_mon hm; exact meet_le_left' _ rel_refl
  · apply lfp_le_of_le
    apply rel_trans _ (by rw [plfp_unfold] <;> apply rel_refl)
    apply hm
    rw [uplfp, meet_spec]
    apply And.intro
    · rw [meet_spec]
      exact And.intro (meet_le_left' _ rel_refl) (meet_le_right' _ h)
    · exact meet_le_right' _ rel_refl

theorem plfp_acc [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) l r
  (obg : ∀ φ, φ ⊑ r → φ ⊑ l → plfp f (hm := hm) φ ⊑ l) : plfp f (hm := hm) r ⊑ l := by
  rw [plfp_acc_aux hm]
  apply obg
  · apply meet_le_left' _ rel_refl
  · apply meet_le_right' _ rel_refl

-- tactics
open Lean Lean.Elab

private inductive paco_mark : Prop
| mk_paco_mark

end Lean4Itree

/-- introduce a new fact, given the witness for that fact -/
def Lean.MVarId.introFact (mvarId : MVarId) (fact : Expr) : MetaM MVarId :=
  mvarId.withContext do
    let t ← Meta.inferType fact
    let (_, mvarIdNew) ← MVarId.intro1P $ ← mvarId.assert Name.anonymous t fact
    return mvarIdNew

/--
Introduce a new fact, and a new goal to prove that fact
the new goal is the first return value.
-/
def Lean.MVarId.introFactWithNewGoal (mvarId : MVarId) (factType : Expr) : MetaM (MVarId × MVarId) :=
  mvarId.withContext do
    let p ← Meta.mkFreshExprSyntheticOpaqueMVar factType
    let (_, mvarIdNew) ← MVarId.intro1P $ ← mvarId.assert Name.anonymous factType p
    return (p.mvarId!, mvarIdNew)

namespace Lean4Itree

open Lean Lean.Elab

/-- Initialise a parameterized-coinduction proof: mark the context and unfold the
goal's `lfp_monotone` fixed point so the Paco combinators can act on it. -/
elab "pinit" : tactic =>
  Tactic.liftMetaTactic λ mvarId => do
    let mark := Expr.const ``paco_mark.mk_paco_mark []
    let mvarId ← mvarId.introFact mark
    let originalHypNum := Meta.getIntrosSize (← mvarId.getType)
    let (_, mvarId) ← mvarId.introNP originalHypNum
    let goalType ← mvarId.getType
    let goalType := goalType.cleanupAnnotations
    let goalHead := goalType.getAppFn
    let Expr.const c _ := goalHead | throwError "{goalHead} is not a defined constant"
    let expanded ← Meta.deltaExpand goalType (c == ·)
    unless expanded.isAppOf ``Lean.Order.lfp_monotone do
      throwError "{expanded} is not constructed with lfp_monotone"
    let mvarId ← mvarId.deltaTarget (c == ·)
    return [mvarId]

/-- Introduce the `plfp_acc` accumulation hypothesis for the current goal,
threading the goal's complete-lattice instance and monotonicity proof. -/
elab "pcofixIntroAcc" : tactic =>
  Tactic.withMainContext do
    let goalType ← Tactic.getMainTarget
    let goalType := goalType.cleanupAnnotations
    -- `plfp f (hm := ...) r` is applied as `@plfp α inst f hm r`, so the goal head
    -- carries the complete-lattice instance (`[1]`), the functor (`[2]`) and the
    -- monotonicity proof (`[3]`). We thread the *goal's* lattice instance through
    -- `plfp_acc` (rather than re-synthesising it) so that coinductive fixpoints,
    -- whose order is `ReverseImplicationOrder`, are not silently elaborated with
    -- the default `ImplicationOrder` — that mismatch flips the `rel` direction and
    -- breaks the subsequent `apply`.
    let instArg := goalType.getAppArgs[1]!
    let fArg := goalType.getAppArgs[2]!
    let hmArg := goalType.getAppArgs[3]!
    let porderArg ← Meta.mkAppOptM ``Lean.Order.CompleteLattice.toPartialOrder
      #[none, some instArg]
    -- Ascribe the monotonicity proof with its expected `monotone f` type (using the
    -- goal's partial order) so that `plfp_acc`'s `hm` argument unifies directly.
    let hmType ← Meta.mkAppOptM ``Lean.Order.monotone
      #[none, some porderArg, none, some porderArg, some fArg]
    let hmArg ← Meta.mkExpectedTypeHint hmArg hmType
    let accBody ← Meta.mkAppOptM ``plfp_acc
      #[none, some instArg, some fArg, some hmArg]
    let some markId := (← getLCtx).findDecl? (λ decl =>
      match decl.type with
      | .const ``paco_mark _ => some decl.fvarId
      | _ => none) | throwError "unreachable"
    -- accType and accBody should not have dependencies below markId
    let (_, hasDep) := (← getLCtx).foldr (λ ldecl (found, hasDep) =>
      let fvar := ldecl.fvarId
      if found then (found, hasDep)
      else if fvar == markId then (true, hasDep)
      else (false, hasDep || hmArg.containsFVar fvar)
    ) (false, false)
    if hasDep then
      throwError "{hmArg}, the proof of monotonicity should not depend on anything that is generalized"
    Tactic.liftMetaTactic λ mvarId => do
      let (_, mvarId) ← mvarId.revertAfter markId
      let mvarId ← mvarId.clear markId
      let mvarId ← mvarId.introFact accBody
      return [mvarId]

/-- Repackage the coinduction goal into the existential relation expected by the
accumulation hypothesis, producing the obligation, converter and main subgoals. -/
elab "pcofixWrap" : tactic =>
  Tactic.withMainContext do
    let goalType ← Tactic.getMainTarget
    let goalType := goalType.cleanupAnnotations
    let (packer, packedGoalType, accArgType) ←
      Meta.forallTelescope goalType λ args conc => do
        let varNames ← args.mapM (·.fvarId!.getUserName)
        let packer : Meta.ArgsPacker := {varNamess := #[varNames]}
        let ty := conc.cleanupAnnotations.getAppArgs[0]!
        pure (packer, ← Meta.ArgsPacker.uncurryType packer #[goalType], ty)
    let packedGoalType ← instantiateMVars packedGoalType.cleanupAnnotations
    let accArgType ← instantiateMVars accArgType.cleanupAnnotations
    let toPacked ← Meta.withLocalDecl `x BinderInfo.default packedGoalType λ x => do
      let body ← Meta.ArgsPacker.curry packer x
      Meta.mkLambdaFVars #[x] body
    let (accArg, unpacker, converter) ← Meta.forallTelescope accArgType λ accArgs _ => do
      Meta.forallTelescope packedGoalType λ packedArg goalConc => do
        let goalArgs := goalConc.cleanupAnnotations.getAppArgs[5:].toArray
        if goalArgs.size != accArgs.size then
          throwError "pcofixWrap, {goalArgs} and {accArgs} have different length"
        let anded ← Array.foldlM (λ acc (accArg, goalArg) => do
          let eq ← Meta.mkEq accArg goalArg
          pure (mkAnd eq acc)
        ) (.const ``True []) (Array.zip accArgs goalArgs)
        let exBody ← Meta.mkLambdaFVars packedArg anded
        let ex ← Meta.mkAppM ``Exists #[exBody]
        let (unpacker, converter) ← Meta.withLocalDecl `φ BinderInfo.default accArgType λ φ => do
          let leftBody ← mkArrow ex (mkAppN φ accArgs)
          let left ← Meta.mkForallFVars accArgs leftBody
          let rightPacked ← Meta.mkForallFVars packedArg (mkAppN φ goalArgs)
          let right ← Meta.ArgsPacker.curryType packer rightPacked
          let toPacked ← Meta.withLocalDecl `f BinderInfo.default right[0]! λ f => do
            let body ← Meta.ArgsPacker.uncurry packer #[f]
            Meta.mkLambdaFVars #[f] body
          let toUnpacked ← Meta.withLocalDecl `f BinderInfo.default rightPacked λ f => do
            let body ← Meta.ArgsPacker.curry packer f
            Meta.mkLambdaFVars #[f] body
          let iffType ← Meta.inferType toUnpacked
          let some (a, b) := iffType.arrow? | throwError "unreachable"
          let iffIntro := Expr.const ``Iff.intro []
          let unpacker ← Meta.mkLambdaFVars #[φ] (mkApp4 iffIntro a b toUnpacked toPacked)
          let converter ← Meta.mkForallFVars #[φ] (mkIff left rightPacked)
          pure (unpacker, converter)
        let accArg ← Meta.mkLambdaFVars accArgs ex
        pure (accArg, unpacker, converter)
    let some accDecl := (← getLCtx).lastDecl | throwError "unreachable"
    let accId := accDecl.fvarId
    Tactic.liftMetaTactic λ mvarId => do
      let [mvarId] ← mvarId.apply toPacked | throwError "unreachable"
      let (_, mvarId) ← mvarId.intros
      let [mvarMain, mvarPf] ← mvarId.apply (.app (.fvar accId) accArg) {} | throwError "unreachable"
      let mvarMain ← mvarMain.cleanup
      let mvarMain ← mvarMain.introFact unpacker
      let (converter, mvarMain) ← mvarMain.introFactWithNewGoal converter
      return [mvarPf, converter, mvarMain]

/-- Split the most recently introduced hypothesis, which must be a conjunction,
into its two components and clear the original. -/
elab "destructLastAnd" : tactic =>
  Tactic.liftMetaTactic λ mvarId => do
    let some last := (← getLCtx).lastDecl | throwError "unreachable"
    let lastId := last.fvarId
    let lastType ← lastId.getType
    unless lastType.isAppOf ``And do
      throwError "constructor is not and"
    let left ← Meta.mkAppM ``And.left #[.fvar lastId]
    let right ← Meta.mkAppM ``And.right #[.fvar lastId]
    let mvarId ← mvarId.introFact left
    let mvarId ← mvarId.introFact right
    let mvarId ← mvarId.clear lastId
    return [mvarId]

/-- The Paco coinduction tactic: starts a parameterized-coinduction proof and
introduces the coinduction hypothesis under the name `cih`. -/
macro "pcofix" cih:ident : tactic => `(tactic|(
  pinit; rw [@plfp_init] at *; pcofixIntroAcc; pcofixWrap
  rename_i x; exists x -- proof for plfp_acc
  intros; constructor -- proof for converter
  · intro h x; apply h; exists x
  · intro h; intros; rename_i anded; revert anded; intro ⟨_, anded⟩
    repeat (destructLastAnd; rename_i h' _; subst h')
    apply h; try assumption
  rename_i unpacker converter -- main goal
  intro $(mkIdent `φ) dummy _h
  have $cih := (converter _).mp _h
  refine ((converter ?_).mpr ?_)
  rw [unpacker] at *
  simp only at *
  clear unpacker converter dummy _h
))

/-- Unfold the parameterized least fixed point once in the goal. -/
macro "pfold" : tactic => `(tactic|(rw [@plfp_unfold]))
/-- Unfold the parameterized least fixed point once in a hypothesis. -/
syntax "punfold" " at " ident : tactic
macro_rules
| `(tactic| punfold at $h:ident) =>
  `(tactic| rw [@plfp_unfold] at $h:ident)

/-- Initialise a parameterized-coinduction proof from a fixed-point hypothesis `h`. -/
elab "pinit" " at " h:ident : tactic =>
  Tactic.withMainContext do
    let some hyp := (← getLCtx).findDecl? (λ ldecl =>
      if ldecl.userName == h.getId then some ldecl.fvarId
      else none) | throwError "Cannot find hypothesis of name {h.getId}"
    let hypType ← hyp.getType
    let hypType ← instantiateMVars hypType.cleanupAnnotations
    let hypHead := hypType.getAppFn
    let Expr.const c _ := hypHead | throwError "{hypHead} is not a defined constant"
    let expanded ← Meta.deltaExpand hypType (c == ·)
    unless expanded.isAppOf ``Lean.Order.lfp_monotone do
      throwError "{expanded} is not constructed with lfp_monotone"
    Tactic.liftMetaTactic λ mvarId => do
      let mvarId ← mvarId.deltaLocalDecl hyp (c == ·)
      return [mvarId]
    Tactic.evalTactic <| ← `(tactic|rw [@plfp_init] at $h:ident)

/-- Clear the residual `⊤ₚ` meet from a `uplfp` hypothesis, leaving the plain
parameterized fixed point. -/
syntax "pclearbot" " at " ident : tactic
macro_rules
| `(tactic| pclearbot at $h:ident) =>
  `(tactic|
      simp only [uplfp] at $h:ident;
      rw [@Lean.Order.CompleteLattice.meet_comm, @Lean.Order.CompleteLattice.meet_top] at $h:ident)

/-- Introduce the disjunction lemma `uplfp_goal` for the current `uplfp` goal,
threading the goal's complete-lattice instance. -/
elab "psplitPrepare" : tactic =>
  Tactic.withMainContext do
    let goalType ← Tactic.getMainTarget
    let goalType := goalType.cleanupAnnotations
    unless goalType.isAppOf ``uplfp do
      throwError "not uplfp"
    -- Thread the goal's complete-lattice instance through `uplfp_goal` (see the
    -- note in `pcofixIntroAcc`): coinductive fixpoints use `ReverseImplicationOrder`,
    -- so re-synthesising the default instance would flip the order.
    let instArg := goalType.getAppArgs[1]!
    let fArg := goalType.getAppArgs[2]!
    let hmArg := goalType.getAppArgs[3]!
    let porderArg ← Meta.mkAppOptM ``Lean.Order.CompleteLattice.toPartialOrder
      #[none, some instArg]
    let hmType ← Meta.mkAppOptM ``Lean.Order.monotone
      #[none, some porderArg, none, some porderArg, some fArg]
    let hmArg ← Meta.mkExpectedTypeHint hmArg hmType
    -- `uplfp_goal`'s binders are `{α} {r z} [inst] {f} (hm)`. Build the term with
    -- fresh metavariables for the leading implicits (`r`, `z`, solved when the
    -- introduced fact is later used) while pinning the carrier `α`, lattice instance,
    -- functor and monotonicity proof from the goal. The carrier is taken from the
    -- instance's type so it agrees with the goal's `ReverseImplicationOrder` carrier.
    let αArg := (← Meta.inferType instArg).getAppArgs[0]!
    let uplfp_goal ← Meta.mkConstWithFreshMVarLevels ``uplfp_goal
    let rMVar ← Meta.mkFreshExprMVar αArg
    let zMVar ← Meta.mkFreshExprMVar αArg
    let body := mkAppN uplfp_goal #[αArg, rMVar, zMVar, instArg, fArg, hmArg]
    Tactic.liftMetaTactic λ mvarId => do
      let mvarId ← mvarId.introFact body
      return [mvarId]

/-- Discharge a `uplfp` goal by choosing its left (`r`) disjunct. -/
macro "pleft" : tactic =>`(tactic|(
  psplitPrepare
  rename_i _uplfp_goal
  apply _uplfp_goal
  left; repeat intro
  rename_i h; exact h
  clear _uplfp_goal))

/-- Discharge a `uplfp` goal by choosing its right (`plfp`) disjunct. -/
macro "pright" : tactic =>`(tactic|(
  psplitPrepare
  rename_i _uplfp_goal
  apply _uplfp_goal
  right; repeat intro
  rename_i h; exact h
  clear _uplfp_goal))

/-- Prepare a `uplfp` hypothesis for case analysis by exposing the underlying
disjunction `r ∨ plfp f r`. -/
elab "pcasesPrepare" " at " h:ident : tactic =>
  Tactic.withMainContext do
    let some hypType := (← getLCtx).findDecl? (λ ldecl =>
      if ldecl.userName == h.getId then some ldecl.type
      else none) | throwError "Cannot find hypothesis of name {h.getId}"
    let hypHead ← instantiateMVars hypType.cleanupAnnotations
    unless hypHead.isAppOf ``uplfp do
      throwError "{hypHead} is not uplfp"
    let rArg := hypHead.getAppArgs[4]!
    let uplfpHead ← Meta.mkAppOptM ``uplfp <| hypHead.getAppArgs[:5].toArray.map some
    let plfpHead ← Meta.mkAppOptM ``plfp <| hypHead.getAppArgs[:5].toArray.map some
    let head ← Meta.forallTelescope (← Meta.inferType rArg) λ args _ => do
      let plfpBody := mkAppN plfpHead args
      let rBody := mkAppN rArg args
      Meta.mkLambdaFVars args (mkOr rBody plfpBody) -- λ x, ⊤ₚ x ∨ plfp f x
    Tactic.liftMetaTactic λ mvarId => do
      let cola := hypHead.getAppArgs[1]!
      let porder ← Meta.mkAppOptM ``Lean.Order.CompleteLattice.toPartialOrder #[none, some cola]
      let rel ← Meta.mkAppOptM ``Lean.Order.PartialOrder.rel #[none, porder]
      let le := mkApp2 rel head uplfpHead
      let (splitGoal, mvarId) ← mvarId.introFactWithNewGoal le
      return [splitGoal, mvarId]
    Tactic.withoutRecover <| Tactic.evalTactic <| ← `(tactic|(
      simp only [uplfp, Lean.Order.CompleteLattice.meet_spec]
      apply And.intro <;>
      solve
      | repeat intro; left; assumption
      | repeat intro; right; assumption
    ))

/-- Apply the disjunction prepared by `pcasesPrepare` to the hypothesis `h`. -/
elab "pcasesDo" " at " h:ident : tactic =>
  Tactic.withMainContext do
    let some last := (← getLCtx).lastDecl | throwError "unreachable"
    let lastId := last.fvarId
    let some hyp := (← getLCtx).findDecl? (λ ldecl =>
      if ldecl.userName == h.getId then some ldecl.fvarId
      else none) | throwError "unreachable"
    let hypType ← hyp.getType
    let hypType ← instantiateMVars hypType.cleanupAnnotations
    let args := hypType.getAppArgs[5:]
    let applied := mkAppN (.fvar lastId) args
    let applied := mkApp applied (.fvar hyp)
    Tactic.liftMetaTactic λ mvarId => do
      let mvarId ← mvarId.introFact applied
      let mvarId ← mvarId.clear lastId
      let mvarId ← mvarId.clear hyp
      return [mvarId]

/-- Rewrite a `uplfp f r` hypothesis into the disjunction `r ∨ plfp f r`. -/
syntax "pcases" " at " ident : tactic
macro_rules
| `(tactic| pcases at $h:ident) =>
  `(tactic| pcasesPrepare at $h:ident; rename_i $h:ident; pcasesDo at $h:ident)

/-- Reduce a `plfp` goal using monotonicity of the parameterized least fixed point. -/
elab "pmon" : tactic =>
  Tactic.withMainContext do
    let goalType ← Tactic.getMainTarget
    let goalType := goalType.cleanupAnnotations
    unless goalType.isAppOf ``plfp do
      throwError "{goalType} is not plfp"
    let cola := goalType.getAppArgs[1]!
    let monArg := goalType.getAppArgs[3]!
    let monHead ← Meta.mkAppOptM ``plfp_mon <| #[none, cola, none, monArg]
    Tactic.liftMetaTactic λ mvarId => do
      let mvarIds ← mvarId.apply monHead
      return mvarIds

/-- Close a goal of the form `x ⊑ ⊤ₚ` using the top-element specification. -/
elab "ptop" : tactic =>
  Tactic.withMainContext do
    let goalType ← Tactic.getMainTarget
    let goalType := goalType.cleanupAnnotations
    unless goalType.isAppOf ``Lean.Order.PartialOrder.rel do
      throwError "{goalType} is not partial order"
    let topArg := goalType.getAppArgs[3]!.cleanupAnnotations
    unless topArg.isAppOf ``Lean.Order.CompleteLattice.top do
      throwError "{goalType} is not CompleteLattice.top_spec"
    let cola := topArg.getAppArgs[1]!
    let le_top ← Meta.mkAppOptM ``Lean.Order.CompleteLattice.top_spec <| #[none, cola]
    Tactic.liftMetaTactic λ mvarId => do
      let mvarIds ← mvarId.apply le_top
      return mvarIds
