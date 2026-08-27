/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Many-sorted matching logic, and the semantic half of Proposition 30.
arXiv:2608.13306v1, Section 8.

Proposition 30 is the paper's SHARPNESS result: it shows the one-sort hypothesis
of Corollary 15 is essential, by exhibiting a three-sorted theory with
`Γ ⊨ φ` and `Γ ⊬ φ`.

  "**Proposition 30.** Let the sorts be b, a, c with symbols f : b → a and
   g : b → c, and put
       Γ = {∀x:b ∀y:b. f(x ∧ y)},   φ = ∀x:b ∀y:b. (g(x) ↔ g(y)).
   Then Γ is satisfiable, Γ ⊨ φ, and Γ ⊬ φ."

This file carries the many-sorted syntax and semantics and the two SEMANTIC
claims — satisfiability and entailment. The third claim, non-derivability, needs
the many-sorted Figure 2 and is left to a later file; the paper proves it by a
"sort feeding" induction on derivations.

DESIGN RULING. Patterns are INDEXED BY SORT (`MPattern S Var s`) rather than
untyped with a separate sorting judgement. The whole non-derivability argument
turns on "the sort of a line in a derivation", so making the sort intrinsic is
what will keep that induction honest. The cost is dependent-type plumbing in the
valuation update, which is confined to `mupdate` below.

Statements pinned before any proof was attempted.
-/
import LeanPool.MatchingLogic.Core

/-!
# MatchingLogic.Sorted
-/

namespace MatchingLogic
namespace Sorted

/-- A many-sorted finitary signature. -/
structure MSignature where
  /-- The type of sorts. -/
  Srt : Type
  /-- The type of operation symbols. -/
  Sym : Type
  /-- The number of arguments of each operation symbol. -/
  arity : Sym → Nat
  /-- The sort of each argument position. -/
  argSort : (σ : Sym) → Fin (arity σ) → Srt
  /-- The result sort of each operation symbol. -/
  resSort : Sym → Srt

variable {S : MSignature} {Var : Type}

/-- Patterns, indexed by their sort.  `ex x s' φ` binds `x` AT SORT `s'` inside
a pattern `φ` of sort `s`; the bound sort need not be the sort of the body, and
in Proposition 30 it is not. -/
inductive MPattern (S : MSignature) (Var : Type) : S.Srt → Type where
  | var : Var → (s : S.Srt) → MPattern S Var s
  | app : (σ : S.Sym) →
      ((i : Fin (S.arity σ)) → MPattern S Var (S.argSort σ i)) →
      MPattern S Var (S.resSort σ)
  | imp : {s : S.Srt} → MPattern S Var s → MPattern S Var s → MPattern S Var s
  | bot : {s : S.Srt} → MPattern S Var s
  | ex : {s : S.Srt} → Var → (s' : S.Srt) → MPattern S Var s → MPattern S Var s

namespace MPattern
variable {s : S.Srt}
/-- Sorted negation. -/
abbrev nt (φ : MPattern S Var s) : MPattern S Var s := imp φ bot
/-- Sorted truth. -/
abbrev tp : MPattern S Var s := imp bot bot
/-- Sorted conjunction. -/
abbrev and (φ ψ : MPattern S Var s) : MPattern S Var s := nt (imp φ (nt ψ))
/-- Sorted disjunction. -/
abbrev orP (φ ψ : MPattern S Var s) : MPattern S Var s := imp (nt φ) ψ
/-- Sorted biconditional. -/
abbrev iff (φ ψ : MPattern S Var s) : MPattern S Var s := and (imp φ ψ) (imp ψ φ)
/-- Sorted universal quantification. -/
abbrev al (x : Var) (s' : S.Srt) (φ : MPattern S Var s) : MPattern S Var s :=
  nt (ex x s' (nt φ))
end MPattern

/-- A many-sorted model: a nonempty carrier per sort, and each symbol
interpreted from its argument sorts to subsets of its result sort. -/
structure MModel (S : MSignature) where
  /-- The carrier type at each sort. -/
  carrier : S.Srt → Type
  nonempty : ∀ s, Nonempty (carrier s)
  /-- The set-valued interpretation of each operation symbol. -/
  interp : (σ : S.Sym) →
    ((i : Fin (S.arity σ)) → carrier (S.argSort σ i)) → Set (carrier (S.resSort σ))

/-- A sorted valuation. -/
abbrev MVal (M : MModel S) (Var : Type) : Type := (s : S.Srt) → Var → M.carrier s

/-- Updating a sorted valuation at one variable of one sort.  This is the only
place the sort indexing costs anything: the new value has sort `s'`, so it can
only be installed at sort `s'`, and the equality has to be transported. -/
noncomputable def mupdate (M : MModel S) (ρ : MVal M Var) (s' : S.Srt) (x : Var)
    (a : M.carrier s') : MVal M Var :=
  letI := Classical.decEq S.Srt
  letI := Classical.decEq Var
  fun t y => if y = x then (if ht : t = s' then ht ▸ a else ρ t y) else ρ t y

/-- The pointwise extension of a symbol, at its sorts. -/
def MModel.app (M : MModel S) (σ : S.Sym)
    (A : (i : Fin (S.arity σ)) → Set (M.carrier (S.argSort σ i))) :
    Set (M.carrier (S.resSort σ)) :=
  {u | ∃ a : (i : Fin (S.arity σ)) → M.carrier (S.argSort σ i),
        (∀ i, a i ∈ A i) ∧ u ∈ M.interp σ a}

/-- The denotation, sort by sort. -/
noncomputable def mdenote (M : MModel S) (ρ : MVal M Var) :
    {s : S.Srt} → MPattern S Var s → Set (M.carrier s)
  | _, .var x s => {ρ s x}
  | _, .bot => ∅
  | _, .app σ f => M.app σ (fun i => mdenote M ρ (f i))
  | _, .imp φ ψ => (mdenote M ρ φ)ᶜ ∪ mdenote M ρ ψ
  | _, .ex x s' φ => ⋃ a : M.carrier s', mdenote M (mupdate M ρ s' x a) φ

/-- The denotation clause for sorted universal quantification. -/
theorem mdenote_al (M : MModel S) (ρ : MVal M Var) {s : S.Srt}
    (x : Var) (s' : S.Srt) (φ : MPattern S Var s) :
    mdenote M ρ (MPattern.al x s' φ) =
      ⋂ a : M.carrier s', mdenote M (mupdate M ρ s' x a) φ := by
  classical
  simp [mdenote, Set.compl_iUnion]

/-- A many-sorted symbol application is empty if one argument is empty. -/
theorem MModel.app_eq_empty (M : MModel S) (σ : S.Sym)
    (A : (i : Fin (S.arity σ)) → Set (M.carrier (S.argSort σ i)))
    (i : Fin (S.arity σ)) (h : A i = ∅) : M.app σ A = ∅ := by
  ext u
  simp only [MModel.app, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, ha, -⟩
  have hi := ha i
  rw [h] at hi
  exact hi

/-- `M ⊨ φ`: `φ` is total at its own sort under every valuation. -/
def MModel.Sat (M : MModel S) {s : S.Srt} (φ : MPattern S Var s) : Prop :=
  ∀ ρ : MVal M Var, mdenote M ρ φ = Set.univ

/-- `M ⊨ Γ` for a HETEROGENEOUS theory: a set of sorted patterns, each total at
its own sort.  This is the paper's notion — nothing there requires the members of
a theory to share a sort. -/
def MModel.SatSetHet (M : MModel S)
    (Γ : Set ((s : S.Srt) × MPattern S Var s)) : Prop :=
  ∀ p ∈ Γ, M.Sat p.2

/-- `M ⊨ Γ` for a theory whose members all have one sort.  A convenience: it is
what Proposition 30 needs, since its `Γ` is a singleton of sort `a`.  It is a
special case of `SatSetHet`, not a different notion — `satSetHet_homogeneous`
below records that. -/
def MModel.SatSet (M : MModel S) {s : S.Srt} (Γ : Set (MPattern S Var s)) : Prop :=
  ∀ γ ∈ Γ, M.Sat γ

/-- The homogeneous notion is the heterogeneous one restricted to a single
sort.  Without this the restriction in `SatSet` would be silent, and an audit
flagged exactly that. -/
theorem satSetHet_homogeneous (M : MModel S) {s : S.Srt}
    (Γ : Set (MPattern S Var s)) :
    M.SatSet Γ ↔ M.SatSetHet {p | ∃ γ ∈ Γ, p = ⟨s, γ⟩} := by
  constructor
  · intro h p hp
    rcases hp with ⟨γ, hγ, rfl⟩
    exact h γ hγ
  · intro h γ hγ
    exact h ⟨s, γ⟩ ⟨γ, hγ, rfl⟩

/-- `Γ ⊨ φ`, where `Γ` and `φ` may live at DIFFERENT sorts -- which is exactly
the situation Proposition 30 exploits. -/
def MGlobalCons {sΓ sφ : S.Srt} (Γ : Set (MPattern S Var sΓ))
    (φ : MPattern S Var sφ) : Prop :=
  ∀ M : MModel S, M.SatSet Γ → M.Sat φ

/-- Global consequence from a heterogeneous theory. -/
def MGlobalConsHet (Γ : Set ((s : S.Srt) × MPattern S Var s)) {sφ : S.Srt}
    (φ : MPattern S Var sφ) : Prop :=
  ∀ M : MModel S, M.SatSetHet Γ → M.Sat φ

/-! ### The signature of Proposition 30 -/

/-- Three sorts, `b`, `a`, `c`. -/
inductive Srt3 where | b | a | c
  deriving DecidableEq

/-- Two symbols, `f : b → a` and `g : b → c`. -/
inductive Sym3 where | f | g
  deriving DecidableEq

/-- The signature of Proposition 30.  Note NO symbol has an argument of sort
`a`; that is what the non-derivability half will turn on. -/
abbrev S3 : MSignature where
  Srt := Srt3
  Sym := Sym3
  arity := fun _ => 1
  argSort := fun _ _ => Srt3.b
  resSort := fun σ => match σ with | .f => Srt3.a | .g => Srt3.c

/-- `f(ψ)` for `ψ` of sort `b`. -/
abbrev fAp (ψ : MPattern S3 Var Srt3.b) : MPattern S3 Var Srt3.a :=
  MPattern.app (S := S3) Sym3.f (fun _ => ψ)
/-- `g(ψ)` for `ψ` of sort `b`. -/
abbrev gAp (ψ : MPattern S3 Var Srt3.b) : MPattern S3 Var Srt3.c :=
  MPattern.app (S := S3) Sym3.g (fun _ => ψ)

/-- `Γ = {∀x:b ∀y:b. f(x ∧ y)}`, a theory of sort `a`. -/
abbrev Γ3 (x y : Var) : Set (MPattern S3 Var Srt3.a) :=
  { MPattern.al x Srt3.b (MPattern.al y Srt3.b
      (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
        (MPattern.var (S := S3) y Srt3.b)))) }

/-- `φ = ∀x:b ∀y:b. (g(x) ↔ g(y))`, a pattern of sort `c`. -/
abbrev φ3 (x y : Var) : MPattern S3 Var Srt3.c :=
  MPattern.al x Srt3.b (MPattern.al y Srt3.b
    (MPattern.iff (gAp (MPattern.var (S := S3) x Srt3.b))
      (gAp (MPattern.var (S := S3) y Srt3.b))))

/-! ### Proposition 30, semantic half -/

/-- The singleton model used for satisfiability in Proposition 30. -/
abbrev singletonM3 : MModel S3 where
  carrier := fun _ => PUnit
  nonempty := fun _ => ⟨PUnit.unit⟩
  interp := fun _ _ => Set.univ

/-- **Γ is satisfiable.** Take every carrier a singleton and `f`, `g` total. -/
theorem Γ3_satisfiable (x y : Var) :
    ∃ M : MModel S3, M.SatSet (Γ3 (Var := Var) x y) := by
  classical
  refine ⟨singletonM3, ?_⟩
  intro γ hγ
  simp only [Γ3, Set.mem_singleton_iff] at hγ
  subst γ
  intro ρ
  ext u
  simp [MModel.app, mdenote]

/-- **Γ ⊨ φ.**

The paper: if `M_b` had distinct `r, s`, the valuation with `ρ(x) = r`,
`ρ(y) = s` gives `ρ(x ∧ y) = ∅`, and symbols propagate `∅`, so `ρ(f(x ∧ y)) = ∅`,
which is not `M_a` because carriers are nonempty. Hence `M_b` is a singleton,
every valuation sends `x` and `y` to the same element, and `ρ(g(x) ↔ g(y)) = M_c`
for every `ρ`. -/
theorem Γ3_entails_φ3 (x y : Var) (hxy : x ≠ y) :
    MGlobalCons (Γ3 (Var := Var) x y) (φ3 (Var := Var) x y) := by
  classical
  intro M hΓ
  have hγ : M.Sat (MPattern.al x Srt3.b (MPattern.al y Srt3.b
      (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
        (MPattern.var (S := S3) y Srt3.b))))) :=
    hΓ _ (Set.mem_singleton _)
  let ρ0 : MVal M Var := fun t _ => Classical.choice (M.nonempty t)
  have hb : ∀ r s : M.carrier Srt3.b, r = s := by
    intro r s
    by_contra hrs
    let ρrs : MVal M Var := mupdate M (mupdate M ρ0 Srt3.b x r) Srt3.b y s
    have houter := hγ ρ0
    rw [mdenote_al] at houter
    have hx : mdenote M (mupdate M ρ0 Srt3.b x r)
        (MPattern.al y Srt3.b
          (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
            (MPattern.var (S := S3) y Srt3.b)))) = Set.univ := by
      ext u
      constructor
      · intro _
        trivial
      · intro _
        have hu : u ∈ ⋂ a : M.carrier Srt3.b,
            mdenote M (mupdate M ρ0 Srt3.b x a)
              (MPattern.al y Srt3.b
                (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
                  (MPattern.var (S := S3) y Srt3.b)))) := by
          rw [houter]
          trivial
        exact Set.mem_iInter.mp hu r
    rw [mdenote_al] at hx
    have hinner : mdenote M ρrs
        (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
          (MPattern.var (S := S3) y Srt3.b))) = Set.univ := by
      ext u
      constructor
      · intro _
        trivial
      · intro _
        have hu : u ∈ ⋂ a : M.carrier Srt3.b,
            mdenote M
              (mupdate M (mupdate M ρ0 Srt3.b x r) Srt3.b y a)
              (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
                (MPattern.var (S := S3) y Srt3.b))) := by
          rw [hx]
          trivial
        exact Set.mem_iInter.mp hu s
    have hand : mdenote M ρrs
        (MPattern.and (MPattern.var (S := S3) x Srt3.b)
          (MPattern.var (S := S3) y Srt3.b)) = ∅ := by
      ext u
      simp [ρrs, mdenote, mupdate, hxy, hrs]
    have happ : mdenote M ρrs
        (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
          (MPattern.var (S := S3) y Srt3.b))) = ∅ := by
      apply MModel.app_eq_empty M Sym3.f _ ⟨0, Nat.zero_lt_one⟩
      exact hand
    have u : M.carrier Srt3.a := Classical.choice (M.nonempty Srt3.a)
    have hu : u ∈ mdenote M ρrs
        (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
          (MPattern.var (S := S3) y Srt3.b))) := by
      rw [hinner]
      trivial
    rw [happ] at hu
    exact hu
  intro ρ
  have hiff : ∀ ρ' : MVal M Var,
      mdenote M ρ'
        (MPattern.iff (gAp (MPattern.var (S := S3) x Srt3.b))
          (gAp (MPattern.var (S := S3) y Srt3.b))) = Set.univ := by
    intro ρ'
    have hval : ρ' Srt3.b x = ρ' Srt3.b y := hb _ _
    ext u
    simp [mdenote, hval]
  rw [mdenote_al]
  apply Set.eq_univ_of_forall
  intro u
  simp only [Set.mem_iInter]
  intro r
  rw [mdenote_al]
  simp only [Set.mem_iInter]
  intro s
  rw [hiff]
  trivial

end Sorted
end MatchingLogic
