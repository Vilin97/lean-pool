/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/

import LeanPool.ZFLean.Basic
import LeanPool.ZFLean.Booleans
import LeanPool.ZFLean.Integers
import LeanPool.ZFLean.Functions

/-!
# LeanPool.ZFLean.Sum

Imported Lean Pool material for `LeanPool.ZFLean.Sum`.
-/

universe u v

namespace ZFSet
/-- Imported ZFLean declaration. -/
def Sum (A B : ZFSet) :=
  {x // x ∈ (ZFSet.prod { ZFBool.false.val } A) ∪ (ZFSet.prod { ZFBool.true.val } B)}
/-- Imported ZFLean declaration. -/
infixr:50 " ⊎ " => Sum

namespace Sum
/-- Imported ZFLean declaration. -/
def inl {A B : ZFSet} (a : {x // x ∈ A}) : Sum A B :=
  ⟨ZFSet.pair ZFBool.false a,
    mem_union.mpr (Or.inl <| pair_mem_prod.mpr ⟨mem_singleton.mpr rfl, a.prop⟩)⟩
/-- Imported ZFLean declaration. -/
def inr {A B : ZFSet} (b : {x // x ∈ B}) : Sum A B :=
  ⟨ZFSet.pair ZFBool.true b,
    mem_union.mpr (Or.inr <| pair_mem_prod.mpr ⟨mem_singleton.mpr rfl, b.prop⟩)⟩

theorem _root_.ZFSet.Sum.inl.injEq
    {A B : ZFSet} {x y : {x // x ∈ A}} : (inl x : A ⊎ B) = inl y ↔ x = y := by
  constructor
  · intro heq
    injection heq with heq
    rw [pair_inj] at heq
    exact Subtype.val_inj.mp heq.2
  · intro
    congr

theorem _root_.ZFSet.Sum.inr.injEq
    {A B : ZFSet} {x y : {x // x ∈ B}} : (inr x : A ⊎ B) = inr y ↔ x = y := by
  constructor
  · intro heq
    injection heq with heq
    rw [pair_inj] at heq
    exact Subtype.val_inj.mp heq.2
  · intro
    congr

theorem cases {A B : ZFSet} (x : A ⊎ B) : x.val.π₂ ∈ A ∨ x.val.π₂ ∈ B := by
  let ⟨x, hx⟩ := x
  rw [mem_union, mem_prod] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
  · rw [mem_union, pair_mem_prod] at hx
    obtain ⟨ha, bA⟩ | hb := hx
    · rw [mem_singleton] at ha
      left
      rwa [π₂_pair]
    · rw [pair_mem_prod, mem_singleton] at hb
      right
      rw [π₂_pair]
      exact hb.2
  · rw [mem_prod] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rw [mem_union, pair_mem_prod] at hx
    obtain ⟨ha, aB⟩ | hb := hx
    · rw [mem_singleton] at ha
      left
      rwa [π₂_pair]
    · rw [pair_mem_prod, mem_singleton] at hb
      right
      rw [π₂_pair]
      exact hb.2
/-- Imported ZFLean declaration. -/
@[cases_eliminator]
noncomputable def casesOn {A B : ZFSet.{u}} {motive : A ⊎ B → Sort v} (x : A ⊎ B)
  (inl : (val : {x // x ∈ A}) → motive (inl val))
  (inr : (val : {x // x ∈ B}) → motive (inr val)) : motive x := by
  by_cases h : x.val.π₁ = ZFBool.false.val
  · have : x.val.π₂ ∈ A := by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · rwa [π₂_pair]
      · dsimp at h
        rw [pair_eta hx, pair_mem_prod, mem_singleton, h] at hx
        nomatch zftrue_ne_zffalse hx.1.symm
    have : x = Sum.inl ⟨x.val.π₂, this⟩ := by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · rw [π₁_pair] at h
        subst a
        congr 2
        dsimp
        rw [π₂_pair]
      · rw [pair_eta hx, pair_mem_prod, mem_singleton, h] at hx
        nomatch zftrue_ne_zffalse hx.1.symm
    rw [this]
    apply inl
  · have x₁_eq_true : x.val.π₁ = ZFBool.true := by
      have := Subtype.property x
      rw [mem_union, mem_prod] at this
      obtain ⟨a, ha, b, hb, eq⟩ | hx := this
      · rw [eq, π₁_pair] at h
        rw [mem_singleton] at ha
        contradiction
      · rw [pair_eta hx, pair_mem_prod, mem_singleton] at hx
        exact hx.1
    have : x.val.π₂ ∈ B := by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · rw [mem_union, pair_mem_prod, mem_singleton] at hx
        obtain ⟨rfl, -⟩ | hb := hx
        · rw [π₁_pair] at x₁_eq_true
          nomatch zftrue_ne_zffalse x₁_eq_true.symm
        · rw [pair_mem_prod] at hb
          rw [π₂_pair]
          exact hb.2
      · rw [pair_eta hx, pair_mem_prod, mem_singleton] at hx
        exact hx.2
    have : x = Sum.inr ⟨x.val.π₂, this⟩ := by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · rw [mem_union, pair_mem_prod, mem_singleton] at hx
        obtain ⟨rfl, -⟩ | hb := hx
        · rw [π₁_pair] at x₁_eq_true
          nomatch zftrue_ne_zffalse x₁_eq_true.symm
        · congr 2
          · dsimp
            rwa [π₁_pair] at x₁_eq_true
          · dsimp
            rw [π₂_pair]
      · congr
        conv_lhs => rw [pair_eta hx]
        rw [pair_inj]
        exact ⟨x₁_eq_true, rfl⟩
    rw [this]
    apply inr

@[simp]
theorem casesOn_of_inl {A B : ZFSet} {motive : A ⊎ B → Sort*} (a : {x // x ∈ A})
  (inl_case : (val : {x // x ∈ A}) → motive (inl val))
  (inr_case : (val : {x // x ∈ B}) → motive (inr val)) :
    casesOn (inl a) inl_case inr_case = inl_case a := by
  rw [casesOn, dite_cond_eq_true (eq_true (by rw [inl, π₁_pair]))]
  dsimp
  rw [cast_eq_iff_heq]
  congr
  unfold inl
  rw [π₂_pair]

@[simp]
theorem casesOn_of_inr {A B : ZFSet} {motive : A ⊎ B → Sort*} (a : {x // x ∈ B})
  (inl_case : (val : {x // x ∈ A}) → motive (inl val))
  (inr_case : (val : {x // x ∈ B}) → motive (inr val)) :
    casesOn (inr a) inl_case inr_case = inr_case a := by
  rw [casesOn, dite_cond_eq_false (eq_false ?_)]
  · dsimp
    rw [cast_eq_iff_heq]
    congr
    unfold inr
    rw [π₂_pair]
  · rw [inr, π₁_pair]
    exact zftrue_ne_zffalse

/-- The equivalence between the ZF disjoint sum and Lean's subtype sum. -/
noncomputable def instEquivSumSubtypeMem {A B : ZFSet} : A ⊎ B ≃ ({x // x ∈ A} ⊕ {x // x ∈ B}) where
  toFun x := by
    cases x with
    | inl a => exact _root_.Sum.inl a
    | inr b => exact _root_.Sum.inr b
  invFun x := by
    cases x with
    | inl a => exact inl a
    | inr b => exact inr b
  left_inv := by
    intro x
    cases x with
    | inl a =>
      beta_reduce
      conv_lhs => rw [casesOn_of_inl]
    | inr b =>
      beta_reduce
      conv_lhs => rw [casesOn_of_inr]
  right_inv := by
    intro x
    cases x with
    | inl a => simp only [casesOn_of_inl]
    | inr b => simp only [casesOn_of_inr]

end Sum
/-- Imported ZFLean declaration. -/
def Option (S : ZFSet) := {∅} ⊎ S

instance {T : ZFSet} : Nonempty (Option T) := ⟨Sum.inl ⟨∅, mem_singleton.mpr rfl⟩⟩

namespace Option
/-- Imported ZFLean declaration. -/
abbrev none {S : ZFSet} : Option S := Sum.inl ⟨∅, mem_singleton.mpr rfl⟩
/-- Imported ZFLean declaration. -/
abbrev some {S : ZFSet} (x : {x // x ∈ S}) : Option S := Sum.inr x

theorem some_ne_none {S : ZFSet} (x : {x // x ∈ S}) : some x ≠ none := by
  unfold some Sum.inr none Sum.inl
  intro h
  injection h with h
  rw [ZFSet.pair_inj] at h
  unfold ZFBool.false ZFBool.true zftrue zffalse at h
  obtain ⟨contr, _⟩ := h
  simp_rw [ZFSet.ext_iff, notMem_empty, iff_false, mem_singleton] at contr
  nomatch contr ∅

theorem casesOn {S : ZFSet} (x : Option S) : x = none ∨ (∃ y, x = some y) := by
  obtain ⟨x, hx⟩ := x
  rw [mem_union] at hx
  rcases hx with hx | hx <;> (
    rw [mem_prod] at hx
    obtain ⟨opt, hopt, val, hval, rfl⟩ := hx
    rw [mem_singleton] at hopt
    subst hopt
    rw [mem_union, pair_mem_prod] at hx)
  · left
    unfold none Sum.inl
    congr
    rcases hx with hx | hx
    · exact mem_singleton.mp hx.right
    · rw [pair_mem_prod, mem_singleton] at hx
      absurd hx.left
      unfold ZFBool.false ZFBool.true zftrue zffalse
      intro contr
      simp_rw [ZFSet.ext_iff, notMem_empty, false_iff, mem_singleton] at contr
      nomatch contr ∅
  · right
    rcases hx with hx | hx
    · rw [mem_singleton] at hx
      absurd hx.left
      unfold ZFBool.false ZFBool.true zftrue zffalse
      intro contr
      simp_rw [ZFSet.ext_iff, notMem_empty, iff_false, mem_singleton] at contr
      nomatch contr ∅
    · rw [pair_mem_prod] at hx
      unfold some Sum.inr
      exists ⟨val, hx.right⟩

-- theorem ZFInt.into.injective : Function.Injective into := into_inj
-- theorem ZFInt.outof.injective : Function.Injective outof := outof_inj

open Classical in
/-- Imported ZFLean declaration. -/
noncomputable abbrev the {S : ZFSet} (S_nemp : S ≠ ∅) (x : Option S) : {x // x ∈ S} :=
  if isNone : x = none then
    ⟨ε S, epsilon_spec (nonempty_exists_iff.mp S_nemp)⟩
  else choose (Or.resolve_left (casesOn x) isNone)



open Classical in
private noncomputable def into {T : ZFSet} : Option T → _root_.Option {x // x ∈ T} := fun x ↦
  if hx : x = none then .none else .some <| Classical.choose <| Or.resolve_left (casesOn x) hx

theorem _root_.ZFSet.Option.some.injEq
    {T : ZFSet} {x y : {x // x ∈ T}} : some x = some y ↔ x = y := by
  constructor
  · intro heq
    injection heq with heq
    rw [pair_inj] at heq
    exact Subtype.val_inj.mp heq.2
  · intro
    congr

theorem some_val_injEq {T : ZFSet} {x y : {x // x ∈ T}} :
    (some x).val = (some y).val ↔ x = y := by
  constructor
  · intro heq
    exact some.injEq.mp (Subtype.ext heq)
  · intro heq
    rw [heq]

theorem ne_none_is_some {T : ZFSet} (x : Option T) : x ≠ none → ∃ y, x = some y := by
  intro h
  obtain ⟨y, hy⟩ := casesOn x
  · contradiction
  · assumption

theorem _root_.ZFSet.Option.into.inj {T : ZFSet} :
    Function.Injective (into : Option T → _root_.Option {x // x ∈ T}) := by
  intro x y heq
  unfold into at heq
  split_ifs at heq with hx hy hy
  · rw [hx, hy]
  · injection heq with heq
    obtain ⟨x, rfl⟩ := ne_none_is_some x hx
    obtain ⟨y, rfl⟩ := ne_none_is_some y hy
    generalize_proofs px py at heq
    rw [Classical.choose_spec px, Classical.choose_spec py]
    congr

theorem _root_.ZFSet.Option.into.surj {T : ZFSet} :
    Function.Surjective (into : Option T → _root_.Option {x // x ∈ T}) := by
  intro y
  unfold into
  cases y with
  | none =>
    exists none
    split_ifs <;> trivial
  | some v =>
    exists (some v)
    split_ifs with h
    · nomatch some_ne_none v h
    · generalize_proofs pv
      rw [← some.injEq.mp <| Classical.choose_spec pv]

theorem _root_.ZFSet.Option.into.bij {T : ZFSet} :
  Function.Bijective (into : Option T → _root_.Option {x // x ∈ T}) := ⟨into.inj, into.surj⟩
/-- Imported ZFLean declaration. -/
noncomputable def EmbeddingZFOptionOption {T : ZFSet} : Option T ↪ _root_.Option {x // x ∈ T} where
  toFun := into
  inj' := into.inj

/-- The equivalence between ZF options and Lean options over a subtype. -/
noncomputable def instEquivZFOptionOption {T : ZFSet} :
    Option T ≃ _root_.Option {x // x ∈ T} where
  toFun := into
  invFun := Function.invFun into
  left_inv := Function.leftInverse_invFun into.inj
  right_inv := Function.rightInverse_invFun into.surj



private def outof {T : ZFSet} : _root_.Option {x // x ∈ T} → Option T
  | .some ⟨x, hx⟩ => some ⟨x, hx⟩
  | .none => none

theorem _root_.ZFSet.Option.outof.inj {T : ZFSet} :
    Function.Injective (outof : _root_.Option {x // x ∈ T} → Option T) := by
  intro x y heq
  cases x <;> cases y <;> unfold outof at heq
  · rfl
  · injection heq with heq
    rw [pair_inj] at heq
    absurd heq.1
    unfold ZFBool.false ZFBool.true zftrue zffalse
    intro contr
    rw [Subtype.val_inj] at contr
    injection contr with contr
    rw [ZFSet.ext_iff] at contr
    exact (notMem_empty ∅) <| (mem_singleton.eq ▸ contr ∅).mpr rfl
  · injection heq with heq
    rw [pair_inj] at heq
    absurd heq.1
    unfold ZFBool.false ZFBool.true zftrue zffalse
    intro contr
    rw [Subtype.val_inj] at contr
    injection contr with contr
    rw [ZFSet.ext_iff] at contr
    exact (notMem_empty ∅) <| (mem_singleton.eq ▸ contr ∅).mp rfl
  · injection heq with heq
    rw [pair_inj] at heq
    have := Subtype.val_inj.mp <| Subtype.mk_eq_mk.mp <| Subtype.val_inj.mp heq.2
    congr

theorem _root_.ZFSet.Option.outof.surj {T : ZFSet} :
    Function.Surjective (outof : _root_.Option {x // x ∈ T} → Option T) := by
  intro y
  unfold outof
  rcases y.casesOn with rfl | ⟨x, rfl⟩
  · exists .none
  · exists .some x

theorem _root_.ZFSet.Option.outof.bij {T : ZFSet} :
  Function.Bijective (outof : _root_.Option {x // x ∈ T} → Option T) := ⟨outof.inj, outof.surj⟩
/-- Imported ZFLean declaration. -/
def EmbeddingOptionZFOption {T : ZFSet} : _root_.Option {x // x ∈ T} ↪ Option T where
  toFun := outof
  inj' := outof.inj

/-- The equivalence between Lean options over a subtype and ZF options. -/
noncomputable def instEquivOptionZFOption {T : ZFSet} :
    _root_.Option {x // x ∈ T} ≃ Option T where
  toFun := outof
  invFun := Function.invFun outof
  left_inv := Function.leftInverse_invFun outof.inj
  right_inv := Function.rightInverse_invFun outof.surj
/-- Imported ZFLean declaration. -/
abbrev toZFSet (T : ZFSet) :
  ZFSet := (ZFSet.prod { ZFBool.false.val } {∅}) ∪ (ZFSet.prod { ZFBool.true.val } T)

open Classical in
/-- Imported ZFLean declaration. -/
noncomputable def flift {A B : ZFSet} (f : ZFSet)
  (hf : IsFunc A B f := by zfun) :
    {f' : ZFSet // IsFunc (Option.toZFSet A) (Option.toZFSet B) f'} :=
  let f' : ZFSet :=
    λᶻ: Option.toZFSet A → Option.toZFSet B
      |          x       ↦ if hx : x ∈ Option.toZFSet A then
                              if isSome : ∃ y, ⟨x, hx⟩ = some y then
                                let ⟨y, hy⟩ := Classical.choose isSome
                                some (S := B) (@ᶻf ⟨y, by rwa [ZFSet.is_func_dom_eq]⟩) |>.val
                              else none (S := B).val
                            else ∅
  have hf' : IsFunc (Option.toZFSet A) (Option.toZFSet B) f' := by
    apply ZFSet.lambda_isFunc
    intro x hx
    rw [dite_cond_eq_true (eq_true hx)]
    split_ifs with isSome <;> apply SetLike.coe_mem
  ⟨f', hf'⟩

theorem flift_bijective {f A B : ZFSet} (hf : IsFunc A B f) :
    (ZFSet.Option.flift f).val.IsBijective (Subtype.property _) ↔ f.IsBijective hf where
  mp := by
    rintro ⟨hinj, hsurj⟩
    and_intros
    · intro x y z hx hy hz xz yz
      specialize hinj (Option.some ⟨x, hx⟩).val (Option.some ⟨y, hy⟩).val (Option.some ⟨z, hz⟩).val
        (SetLike.coe_mem _) (SetLike.coe_mem _) (SetLike.coe_mem _) ?_ ?_
      · rw [flift, lambda_spec]
        simp only [SetLike.coe_mem, ↓reduceDIte, Subtype.coe_eta, some.injEq, exists_eq',
          Classical.choose_eq', SetLike.coe_eq_coe, true_and]
        change (ZFSet.Option.some ⟨z, hz⟩ : ZFSet.Option B) =
          ZFSet.Option.some (@ᶻf ⟨x, by rwa [ZFSet.is_func_dom_eq]⟩)
        rw [ZFSet.Option.some.injEq]
        symm
        exact fapply.of_pair _ xz
      · rw [flift, lambda_spec]
        simp only [SetLike.coe_mem, ↓reduceDIte, Subtype.coe_eta, some.injEq, exists_eq',
          Classical.choose_eq', SetLike.coe_eq_coe, true_and]
        change (ZFSet.Option.some ⟨z, hz⟩ : ZFSet.Option B) =
          ZFSet.Option.some (@ᶻf ⟨y, by rwa [ZFSet.is_func_dom_eq]⟩)
        rw [ZFSet.Option.some.injEq]
        symm
        exact fapply.of_pair _ yz
      · have hxy : (⟨x, hx⟩ : {x // x ∈ A}) = ⟨y, hy⟩ := some_val_injEq.mp hinj
        exact Subtype.ext_iff.mp hxy
    · intro y hy
      have : (Option.some ⟨y, hy⟩).val ∈ Option.toZFSet B :=
        SetLike.coe_mem _
      obtain ⟨x, hx, xy⟩ := hsurj _ this
      rw [flift, lambda_spec, dite_cond_eq_true (eq_true hx)] at xy
      obtain ⟨-, -, eq⟩ := xy
      split_ifs at eq with issome
      · have eq_val := congrArg Subtype.val (some_val_injEq.mp eq)
        dsimp at eq_val
        obtain rfl := eq_val
        use (Classical.choose issome).val
        and_intros
        · apply SetLike.coe_mem
        · apply fapply.def
      · exact False.elim (ZFSet.Option.some_ne_none _ (Subtype.ext eq))
  mpr := by
    intro hbij
    rw [bijective_exists1_iff] at hbij ⊢
    intro y hy
    obtain eq | ⟨⟨y, hy⟩, eq⟩ := Option.casesOn ⟨y, hy⟩
    · have eq_val := congrArg Subtype.val eq
      dsimp [none, Sum.inl] at eq_val
      obtain rfl := eq_val
      use (@none A).val
      and_intros
      · apply SetLike.coe_mem
      · rw [flift, lambda_spec, dite_cond_eq_true (eq_true (SetLike.coe_mem _))]
        and_intros
        · apply SetLike.coe_mem
        · exact hy
        · split_ifs with isnone
          · obtain ⟨_, contr⟩ := isnone
            change none = some _ at contr
            nomatch ZFSet.Option.some_ne_none _ contr.symm
          · rfl
      · rintro y ⟨hy, pair⟩
        rw [flift, lambda_spec] at pair
        obtain ⟨-, -, eq⟩ := pair
        rw [dite_cond_eq_true (eq_true hy)] at eq
        split_ifs at eq with issome
        · exact False.elim (ZFSet.Option.some_ne_none _ (Subtype.ext eq.symm))
        · have this : (⟨y, hy⟩ : Option A) = none := by
            by_contra hnone
            exact issome (ZFSet.Option.ne_none_is_some _ hnone)
          exact congrArg Subtype.val this
    · have eq_val := congrArg Subtype.val eq
      dsimp [some, Sum.inr] at eq_val
      obtain rfl := eq_val
      obtain ⟨x, ⟨hx, fxy⟩, x_unq⟩ := hbij y ‹_›
      use (Option.some ⟨x, hx⟩).val
      and_intros
      · apply SetLike.coe_mem
      · rw [flift, lambda_spec, dite_cond_eq_true (eq_true (SetLike.coe_mem _))]
        and_intros
        · apply SetLike.coe_mem
        · exact hy
        · split_ifs with isnone
          · have := Classical.choose_spec isnone
            change some _ = some _ at this
            rw [ZFSet.Option.some.injEq, Subtype.ext_iff] at this
            dsimp at this
            rw [this] at fxy
            have fxy_apply := fapply.of_pair (is_func_is_pfunc hf) fxy
            dsimp [ZFSet.Option.some, Sum.inr]
            rw [pair_inj]
            exact ⟨rfl, (congrArg Subtype.val fxy_apply).symm⟩
          · exact False.elim (isnone ⟨⟨x, hx⟩, Subtype.ext rfl⟩)
      · rintro z ⟨hz, fzy⟩
        rw [flift, lambda_spec] at fzy
        obtain ⟨-, -, eq⟩ := fzy
        rw [dite_cond_eq_true (eq_true hz)] at eq
        split_ifs at eq with issome
        · have z_eq_some := congrArg Subtype.val (Classical.choose_spec issome)
          have chosen_pair : (Classical.choose issome).val.pair y ∈ f := by
            have hdom : (Classical.choose issome).val ∈ f.Dom := by
              rw [is_func_dom_eq hf]
              exact (Classical.choose issome).property
            have hpair := fapply.def (is_func_is_pfunc hf) hdom
            dsimp [ZFSet.Option.some, Sum.inr] at eq
            rw [pair_inj] at eq
            rw [eq.2]
            exact hpair
          have chosen_eq : (Classical.choose issome).val = x :=
            x_unq _ ⟨(Classical.choose issome).property, chosen_pair⟩
          trans (ZFSet.Option.some (Classical.choose issome)).val
          · exact z_eq_some
          · dsimp [ZFSet.Option.some, Sum.inr]
            rw [pair_inj]
            exact ⟨rfl, chosen_eq⟩
        · dsimp [ZFSet.Option.none, Sum.inl] at eq
          rw [pair_inj] at eq
          exact False.elim (zftrue_ne_zffalse eq.1)

end Option

end ZFSet
