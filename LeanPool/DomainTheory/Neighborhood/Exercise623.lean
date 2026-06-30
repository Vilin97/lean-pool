/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise621
import LeanPool.DomainTheory.Neighborhood.Theorem69

/-!
# Exercise 6.23 (Scott 1981, PRG-19, §6) — the syntactic domain of expressions

> **EXERCISE 6.23.** Construe the initial solution to
> `Exp ≅ N ⊕ ((Exp × Exp) + (Exp × Exp))`
> as a "syntactical domain" of expressions generated from infinitely many
"variables" by means of two
> binary "operation symbols". Given an algebra `D` with two operations `u : D×D →
D` and
> `v : D×D → D`, show how any strict map `s : N → D` determines a unique map
`val(s) : Exp → D` that
> can be regarded as the "evaluation of an expression".

The right-hand functor is `T(X) = N ⊕ ((X×X) + (X×X))`, i.e. in the algebra
`GExpr` of Exercise 6.21,
`Texp N = .oplus (.const N) (.sum (.prod .var .var) (.prod .var .var))`. Reading
the structure map
`k : T(Exp) → Exp` of an algebra through the universal properties of `⊕`, `+`,
`×`:

* the `⊕ N` summand gives a strict **variable map** `s : N → Exp` (the "infinitely
many variables"
  are the tokens / points of `N`);
* the two `(Exp × Exp)` summands, combined by `+`, give two binary **operation
symbols**
  `u, v : Exp × Exp → Exp`.

So an algebra of this functor is exactly *a domain `D` with a strict `s : N → D`
and two binary
operations `u, v : D×D → D`*, and the unique homomorphism `val(s) : Exp → D` is
Scott's "evaluation
of an expression": it sends a variable to its value under `s`, and an `u`/`v`-node
to the `u`/`v` of
the values of its two subexpressions.

## This module (Phase 1 — the domain `Exp` itself)

Following Scott's standing restriction in Exercises 6.19–6.23 to `∅`-free systems
over `{0,1}*` and
*strict* maps (`ScottSys`), and following the structure of **Theorem 6.14** (the
initial solution is
the iterated colimit `𝒟 = ⋃ₙ Tⁿ({Γ})`), we build the concrete solution domain
**for any rooted
`GExpr` functor** `T`:

* `gFix T = ⋃ₙ gFunⁿ({Λ})` — the token set (Exercise 6.20/6.21 fixed point `Γ =
tok(T({Γ}))`);
* `gTower T n = Tⁿ({Γ})` — the iterated-functor tower of `∅`-free systems over
`Str`;
* `gColim T = ⋃ₙ Tⁿ({Γ})` — the colimit system, with `gColim_obj_eq : T(gColim) =
gColim` (the
  structure map is the **identity**, since the two systems are literally equal —
  no carrier transport
  is needed because `ScottSys` keeps the token type fixed at `Str`).

Instantiating at `Texp N` gives `Exp N := gColim (Texp N)` together with the
domain-equation
**isomorphism** `Exp ≅ N ⊕ ((Exp×Exp)+(Exp×Exp))` (`Exp_structure_eq`). The
algebra decomposition
(`s`, `u`, `v`) and the unique evaluation homomorphism `val(s)` (initiality) are
developed in later
phases.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); the
colimit is genuine data
built without `Classical.choice` (the generator `Γ` is the *explicit* Kleene
union, not an
existential witness).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap Domain.Neighborhood.Exercise619
open Domain.Neighborhood.Example62 Domain.Neighborhood.ExampleB Domain.Neighborhood.Exercise510

namespace Exercise619

/-! ## The generator `Γ = ⋃ₙ gFunⁿ({Λ})` (the Exercise 6.20/6.21 fixed point, as
data) -/

/-- **The fixed-point token set `Γ = tok(T({Γ}))`**, as the explicit Kleene union
`⋃ₙ gIter T n`
(no `Classical.choice`). -/
def gFix (T : GExpr) : Set Str := ⋃ n, gIter T n

theorem gFix_nil_mem (T : GExpr) : ([] : Str) ∈ gFix T :=
  Set.mem_iUnion.mpr ⟨0, rfl⟩

theorem gFix_nonempty (T : GExpr) : (gFix T).Nonempty := ⟨[], gFix_nil_mem T⟩

/-- `Γ = tok(T({Γ}))` at the token level: `gFun T Γ = Γ`. -/
theorem gFix_fixed (T : GExpr) (hT : T.RootedConst) : gFun T (gFix T) = gFix T :=
  gFun_iter_fixed T hT

/-! ## The iterated-functor tower `Tⁿ({Γ})` -/

/-- **The one-point generator `{Γ}`** as an object of the category. -/
def gGen (T : GExpr) : ScottSys := singletonSys (gFix T) (gFix_nonempty T)

@[simp] theorem gGen_master (T : GExpr) : (gGen T).sys.master = gFix T := rfl

/-- **`{Γ} ◁ T({Γ})`** — Scott's hypothesis for Theorem 6.14, the base of the
tower. (This is the
content of `gExists_singleton_subsystem`, here at the *explicit* generator `Γ =
gFix T`.) -/
theorem gBase (T : GExpr) (hT : T.RootedConst) : (gGen T).sys ◁ (T.obj (gGen T)).sys := by
  have hmaster : (T.obj (gGen T)).sys.master = gFix T :=
    (gFun_eq_master T (gFix_nonempty T)).symm.trans (gFix_fixed T hT)
  refine ⟨hmaster.symm, ?_, ?_⟩
  · intro X hX
    have heq : X = (T.obj (gGen T)).sys.master := (hX : X = gFix T).trans hmaster.symm
    rw [heq]; exact (T.obj (gGen T)).sys.master_mem
  · intro X Y hX hY _
    change X ∩ Y = gFix T
    rw [show X = gFix T from hX, show Y = gFix T from hY, Set.inter_self]

/-- **The tower `Tⁿ({Γ})`** of `∅`-free systems over `Str`: `T⁰({Γ}) = {Γ}`,
`Tⁿ⁺¹({Γ}) =
T(Tⁿ({Γ}))`. -/
def gTower (T : GExpr) : ℕ → ScottSys
  | 0 => gGen T
  | n + 1 => T.obj (gTower T n)

@[simp] theorem gTower_zero (T : GExpr) : gTower T 0 = gGen T := rfl

@[simp] theorem gTower_succ (T : GExpr) (n : ℕ) : gTower T (n + 1) = T.obj (gTower T n) := rfl

/-- **The basic chain step `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ})`.** Base: `gBase`. Step: `T` is
monotone on domains
(`obj_subsystem`). -/
theorem gChain (T : GExpr) (hT : T.RootedConst) :
    ∀ n, (gTower T n).sys ◁ (gTower T (n + 1)).sys
  | 0 => gBase T hT
  | n + 1 => T.obj_subsystem (gChain T hT n)

/-- Every level of the tower has the same master `Δ = Γ`. -/
theorem gTower_master (T : GExpr) (hT : T.RootedConst) :
    ∀ n, (gTower T n).sys.master = gFix T
  | 0 => rfl
  | n + 1 => ((gChain T hT n).master_eq).symm.trans (gTower_master T hT n)

/-- The tower is a `◁`-chain: `Tⁿ({Γ}) ◁ Tᵐ({Γ})` whenever `n ≤ m`. -/
theorem gTower_le (T : GExpr) (hT : T.RootedConst) {n m : ℕ} (h : n ≤ m) :
    (gTower T n).sys ◁ (gTower T m).sys := by
  induction h with
  | refl => exact Subsystem.refl _
  | step _ ih => exact ih.trans (gChain T hT _)

/-! ## The colimit `𝒟 = ⋃ₙ Tⁿ({Γ})` -/

/-- **The colimit system `𝒟 = ⋃ₙ Tⁿ({Γ})`** as an `∅`-free system over `Str`. A
set is a
neighbourhood exactly when it is a neighbourhood of some level; closure under
consistent intersection
uses that the tower is a chain (any finite collection sits inside one level). -/
def gColim (T : GExpr) (hT : T.RootedConst) : ScottSys where
  sys :=
    { mem := fun X => ∃ n, (gTower T n).sys.mem X
      master := gFix T
      master_mem := ⟨0, (gTower T 0).sys.master_mem⟩
      inter_mem := by
        rintro X Y Z ⟨n, hX⟩ ⟨m, hY⟩ ⟨p, hZ⟩ hsub
        set N := max n (max m p) with hN
        have hXN : (gTower T N).sys.mem X := (gTower_le T hT (le_max_left n _)).sub hX
        have hYN : (gTower T N).sys.mem Y :=
          (gTower_le T hT ((le_max_left m p).trans (le_max_right n _))).sub hY
        have hZN : (gTower T N).sys.mem Z :=
          (gTower_le T hT ((le_max_right m p).trans (le_max_right n _))).sub hZ
        exact ⟨N, (gTower T N).sys.inter_mem hXN hYN hZN hsub⟩
      sub_master := by
        rintro X ⟨n, hX⟩
        rw [← gTower_master T hT n]
        exact (gTower T n).sys.sub_master hX }
  ne := by rintro X ⟨n, hX⟩; exact (gTower T n).ne X hX

@[simp] theorem mem_gColim (T : GExpr) (hT : T.RootedConst) {X : Set Str} :
    (gColim T hT).sys.mem X ↔ ∃ n, (gTower T n).sys.mem X := Iff.rfl

@[simp] theorem gColim_master (T : GExpr) (hT : T.RootedConst) :
    (gColim T hT).sys.master = gFix T := rfl

/-- Each level of the tower is a subdomain of the colimit: `Tⁿ({Γ}) ◁ 𝒟`. -/
theorem gTower_sub_colim (T : GExpr) (hT : T.RootedConst) (n : ℕ) :
    (gTower T n).sys ◁ (gColim T hT).sys where
  master_eq := by rw [gColim_master, gTower_master T hT]
  sub hX := ⟨n, hX⟩
  inter_closed := by
    rintro X Y hX hY ⟨m, hXY⟩
    have hN : (gTower T (max n m)).sys.mem (X ∩ Y) :=
      (gTower_le T hT (le_max_right n m)).sub hXY
    exact (gTower_le T hT (le_max_left n m)).inter_closed hX hY hN

/-! ## The structure isomorphism `T(𝒟) = 𝒟` -/

/-- Two objects of the category with the same underlying system are equal (the
`∅`-freeness field is
a `Prop`). -/
theorem ScottSys.ext {A B : ScottSys} (h : A.sys = B.sys) : A = B := by
  cases A; cases B; cases h; rfl

/-- **`T(𝒟) = 𝒟` at the level of neighbourhood systems.** Membership: continuity
on domains
(`obj_continuous`) along the directed tower turns `T(⋃ₙ Tⁿ({Γ}))` into `⋃ₙ
Tⁿ⁺¹({Γ})`, which has the
same neighbourhoods as `⋃ₙ Tⁿ({Γ})` (the extra `n=0` level `T⁰({Γ})` is absorbed
by the chain step).
Master: both are `Γ` (`gTower_master` through `obj_subsystem` of `Tⁿ({Γ}) ◁ 𝒟`). -/
theorem gColim_obj_sys_eq (T : GExpr) (hT : T.RootedConst) :
    (T.obj (gColim T hT)).sys = (gColim T hT).sys := by
  set ℱ : Set ScottSys := Set.range (gTower T) with hℱ
  have hne : ℱ.Nonempty := ⟨gTower T 0, 0, rfl⟩
  have hsub : ∀ D ∈ ℱ, D.sys ◁ (gColim T hT).sys := by
    rintro D ⟨n, rfl⟩; exact gTower_sub_colim T hT n
  have hdir : DirectedOn (fun a b => a.sys ◁ b.sys) ℱ := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    exact ⟨gTower T (max n m), ⟨max n m, rfl⟩,
      gTower_le T hT (le_max_left n m), gTower_le T hT (le_max_right n m)⟩
  have hU : ∀ X, (gColim T hT).sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X := by
    intro X; constructor
    · rintro ⟨n, hn⟩; exact ⟨gTower T n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨D, ⟨n, rfl⟩, hn⟩; exact ⟨n, hn⟩
  apply NeighborhoodSystem.ext
  · intro W
    rw [T.obj_continuous hdir hne hsub hU W]
    constructor
    · rintro ⟨D, ⟨n, rfl⟩, hn⟩
      -- `T(Tⁿ({Γ})) = Tⁿ⁺¹({Γ})`, a level of the colimit.
      exact ⟨n + 1, hn⟩
    · rintro ⟨n, hn⟩
      -- a colimit neighbourhood at level `n` is, after one chain step, at
      -- `T(Tⁿ({Γ}))`.
      exact ⟨gTower T n, ⟨n, rfl⟩, (gChain T hT n).sub hn⟩
  · -- masters: `(T 𝒟).master = (Tⁿ⁺¹({Γ})).master = Γ = 𝒟.master`, via `obj_subsystem` at `n=0`.
    have h := (T.obj_subsystem (gTower_sub_colim T hT 0)).master_eq
    rw [gColim_master]
    rw [show (T.obj (gTower T 0)) = gTower T 1 from rfl] at h
    rw [← h, gTower_master T hT]

/-- **The structure isomorphism `T(𝒟) ≅ 𝒟` is the identity** (the two objects are
literally
equal). -/
theorem gColim_obj_eq (T : GExpr) (hT : T.RootedConst) : T.obj (gColim T hT) = gColim T hT :=
  ScottSys.ext (gColim_obj_sys_eq T hT)

/-! ## The functor of Exercise 6.23 and the syntactic domain `Exp` -/

/-- **The functor `T(X) = N ⊕ ((X×X) + (X×X))`** of Exercise 6.23, as a `GExpr`
over the variable
domain `N`. The `⊕ N` carries the variables, and the two `(X×X)` summands
(combined by `+`) carry the
two binary operation symbols. -/
def Texp (N : ScottSys) : GExpr :=
  .oplus (.const N) (.sum (.prod .var .var) (.prod .var .var))

/-- `Texp N` is rooted iff the variable domain `N` is (`Λ ∈ tok(N)`, automatic for
the fixed-point
solutions of 6.19–6.22). -/
theorem Texp_rooted {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) : (Texp N).RootedConst :=
  ⟨hN, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

/-- **The syntactic domain of expressions** `Exp = ⋃ₙ Texpⁿ({Γ})`, the initial
solution of
`Exp ≅ N ⊕ ((Exp×Exp)+(Exp×Exp))`. -/
def Exp (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) : ScottSys :=
  gColim (Texp N) (Texp_rooted hN)

/-- **The domain equation `Exp ≅ N ⊕ ((Exp×Exp)+(Exp×Exp))`**, realised as an
equality of systems
(the structure map is the identity). This is the "construe the initial solution"
half of
Exercise 6.23. -/
theorem Exp_structure_eq (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    (Texp N).obj (Exp N hN) = Exp N hN :=
  gColim_obj_eq (Texp N) (Texp_rooted hN)

/-! ## Phase 2 — the strict-map category, the endofunctor `T`, and the algebra
`Exp`

Following Scott (and Exercise 6.17's `StrictDomainObj`), but over the *fixed*
token type `Str`: the
objects are `ScottSys` (∅-free systems over `Str`), the morphisms are **strict**
approximable maps.
Because every object lives over `Str`, all carrier equalities are `rfl` and there
is no `HEq`
transport (the obstruction that made the abstract Theorem 6.14 unusable). The
functor `Texp N` then
becomes a genuine `Endofunctor` of this category, and the colimit `Exp` of Phase 1
— together with the
structure equality `T(Exp) = Exp` — is a `T`-algebra. -/

/-- **The category of `∅`-free domains over `Str` and strict maps.** Morphisms are
strict
approximable
maps (`StrictMap`); identities and associative composition are Theorem 2.5, with
strictness preserved
by `isStrict_idMap`/`isStrict_comp`. The fixed carrier `Str` is what removes all
the carrier-transport
`HEq` that burdens the abstract `Endofunctor DomainObj`. -/
instance : Category ScottSys where
  Hom A B := StrictMap A.sys B.sys
  id A := ⟨idMap A.sys, isStrict_idMap⟩
  comp g f := ⟨g.1.comp f.1, isStrict_comp g.2 f.2⟩
  id_comp f := Subtype.ext (idMap_comp f.1)
  comp_id f := Subtype.ext (comp_idMap f.1)
  assoc h g f := Subtype.ext (comp_assoc h.1 g.1 f.1)

@[simp] theorem ScottSys.id_val (A : ScottSys) :
    (Category.id A : StrictMap A.sys A.sys).1 = idMap A.sys := rfl

@[simp] theorem ScottSys.comp_val {A B C : ScottSys} (g : Category.Hom B C) (f : Category.Hom A B) :
    ((g ⊚ f : StrictMap A.sys C.sys)).1 = g.1.comp f.1 := rfl

/-- The morphism action of `gFunctor T`: a strict `f` is sent to the strict map
`T(f)`. (Typed via
`StrictMap`, which is defeq to the category's `Hom`; this avoids the
class-projection that blocks the
anonymous `.1` on `Category.Hom`.) -/
def gFunctorMap (T : GExpr) {X Y : ScottSys} (f : StrictMap X.sys Y.sys) :
    StrictMap (T.obj X).sys (T.obj Y).sys :=
  ⟨T.map f.1, T.map_isStrict f.1 f.2⟩

/-- **Every `GExpr` is an `Endofunctor` of the strict-map category.** On objects
it is `GExpr.obj`;
on a strict map `f` it is the strict map `T(f)` (`GExpr.map_isStrict`).
Functoriality is
`GExpr.map_id` and `GExpr.map_comp` (the latter needs `g` strict — automatic here,
since every
morphism of this category is strict). -/
def gFunctor (T : GExpr) : Endofunctor ScottSys where
  obj := T.obj
  map := gFunctorMap T
  map_id X := Subtype.ext (T.map_id X)
  map_comp {_ _ _} g f :=
    Subtype.ext (T.map_comp (f : StrictMap _ _).1 (g : StrictMap _ _).2)

@[simp] theorem gFunctor_obj (T : GExpr) (X : ScottSys) : (gFunctor T).obj X = T.obj X := rfl

@[simp] theorem gFunctorMap_val (T : GExpr) {X Y : ScottSys} (f : StrictMap X.sys Y.sys) :
    (gFunctorMap T f).1 = T.map f.1 := rfl

/-- **The endofunctor `T(X) = N ⊕ ((X×X) + (X×X))`** of Exercise 6.23. -/
def TexpF (N : ScottSys) : Endofunctor ScottSys := gFunctor (Texp N)

/-- The identity isomorphism in any category induced by an object equality. -/
def isoOfObjEq {Obj : Type*} [Category Obj] {X Y : Obj} (h : X = Y) : Iso X Y := by
  cases h
  exact ⟨Category.id X, Category.id X, Category.id_comp _, Category.id_comp _⟩

/-- **The structure isomorphism `T(Exp) ≅ Exp`.** Since Phase 1 proved `T(Exp) =
Exp` as objects
(`Exp_structure_eq`), this is the identity isomorphism. -/
def ExpIso (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    Iso ((TexpF N).obj (Exp N hN)) (Exp N hN) :=
  isoOfObjEq (Exp_structure_eq N hN)

/-- **`Exp` as a `T`-algebra** with structure map the isomorphism `T(Exp) ≅ Exp`
(the identity,
since
`T(Exp) = Exp`). This realises Scott's "construe the initial solution as a
syntactic domain of
expressions": `Exp` is an algebra of `T(X) = N ⊕ ((X×X)+(X×X))`. -/
def ExpAlg (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) : TAlgebra (TexpF N) where
  carrier := Exp N hN
  str := (ExpIso N hN).hom

/-! ## Phase 3 — the evaluation homomorphism `val(s)` (existence)

Given any algebra `B = (D, k)` of `T(X) = N ⊕ ((X×X)+(X×X))` — i.e. a domain `D`
carrying (through the
universal properties of `⊕`,`+`,`×`) a strict variable map `s : N → D` and two
binary operations
`u, v : D×D → D` — we build a `T`-algebra homomorphism `val : Exp → D`. This is
Scott's *"evaluation
of an expression"*.

Since Phase 1's structure map `i : T(Exp) → Exp` is the **identity**
(`Exp_structure_eq`), the
homomorphism equation `val ∘ i = k ∘ T(val)` is the fixed-point equation `val = k
∘ T(val) ∘ j`
(`j = i⁻¹`). We solve it directly by the Kleene iteration `valₙ` (`val₀ = ⊥`,
`valₙ₊₁ = k ∘ T(valₙ) ∘ j`) and take `val = ⋃ₙ valₙ`. The fixed-point property
uses *continuity on
maps* (`GExpr.map_continuous`: `T(⋃ valₙ) = ⋃ T(valₙ)`); no projection machinery
is needed for
existence. (Uniqueness — initiality — is the remaining Phase 4.) -/

/-- The structure map of an algebra `B`, as a raw approximable map (its strictness
is
`algStr_strict`).
The ascription to `StrictMap` forces the categorical `Hom` to its underlying
subtype. -/
def algStr (B : TAlgebra (TexpF N)) :
    ApproximableMap ((Texp N).obj B.carrier).sys B.carrier.sys :=
  (B.str : StrictMap ((Texp N).obj B.carrier).sys B.carrier.sys).1

theorem algStr_strict (B : TAlgebra (TexpF N)) : IsStrict (algStr B) :=
  (B.str : StrictMap ((Texp N).obj B.carrier).sys B.carrier.sys).2

/-- The inverse `j = i⁻¹ : Exp → T(Exp)` of the structure isomorphism, as a raw
map. -/
def expInv (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    ApproximableMap (Exp N hN).sys ((Texp N).obj (Exp N hN)).sys :=
  ((ExpIso N hN).inv : StrictMap (Exp N hN).sys ((Texp N).obj (Exp N hN)).sys).1

theorem expInv_strict (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) : IsStrict (expInv N hN) :=
  ((ExpIso N hN).inv : StrictMap (Exp N hN).sys ((Texp N).obj (Exp N hN)).sys).2

/-- The structure map `i : T(Exp) → Exp` as a raw map (the identity, since `T(Exp)
= Exp`). -/
def expHom (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    ApproximableMap ((Texp N).obj (Exp N hN)).sys (Exp N hN).sys :=
  ((ExpIso N hN).hom : StrictMap ((Texp N).obj (Exp N hN)).sys (Exp N hN).sys).1

/-- `j ∘ i = I_{T(Exp)}` at the raw level (from the iso's `hom_inv_id`). -/
theorem expInv_comp_expHom (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    (expInv N hN).comp (expHom N hN) = idMap ((Texp N).obj (Exp N hN)).sys := by
  have h := congrArg (Subtype.val) (ExpIso N hN).hom_inv_id
  exact h

/-- `i ∘ j = I_Exp` at the raw level (from the iso's `inv_hom_id`). -/
theorem expHom_comp_expInv (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    (expHom N hN).comp (expInv N hN) = idMap (Exp N hN).sys := by
  have h := congrArg (Subtype.val) (ExpIso N hN).inv_hom_id
  exact h

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- **The Kleene iterates `valₙ : Exp → D`** of the operator `λh. k ∘ T(h) ∘ j`.
`val₀ = ⊥`,
`valₙ₊₁ = k ∘ T(valₙ) ∘ j`. -/
def descRel : ℕ → ApproximableMap (Exp N hN).sys B.carrier.sys
  | 0 => constMap (Exp N hN).sys B.carrier.sys.bot
  | n + 1 => (algStr B).comp (((Texp N).map (descRel n)).comp (expInv N hN))

@[simp] theorem descRel_succ (n : ℕ) :
    descRel hN B (n + 1) = (algStr B).comp (((Texp N).map (descRel hN B n)).comp (expInv N hN)) :=
  rfl

/-- Every iterate is strict. -/
theorem descRel_isStrict : ∀ n, IsStrict (descRel hN B n)
  | 0 => isStrict_constBot
  | n + 1 => by
      rw [descRel_succ]
      exact isStrict_comp (algStr_strict B)
        (isStrict_comp ((Texp N).map_isStrict _ (descRel_isStrict n)) (expInv_strict N hN))

/-- The constant `⊥` map is below every approximable map (it relates each domain
neighbourhood only
to the codomain master, which every map produces by monotonicity from
`master_rel`). -/
theorem constBot_le {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (g : ApproximableMap V₀ V₁) : constMap V₀ V₁.bot ≤ g := by
  intro X Y hr
  obtain ⟨hX, hY⟩ := hr
  rw [NeighborhoodSystem.mem_bot] at hY
  subst hY
  exact g.mono g.master_rel (V₀.sub_master hX) subset_rfl hX V₁.master_mem

/-- The iterates increase: `valₙ ≤ valₙ₊₁`. -/
theorem descRel_le_succ : ∀ n, descRel hN B n ≤ descRel hN B (n + 1)
  | 0 => constBot_le _
  | n + 1 => by
      rw [descRel_succ, descRel_succ]
      exact comp_mono_gen le_rfl
        (comp_mono_gen ((Texp N).map_mono (descRel_le_succ n)) le_rfl)

/-- The iterates form a `≤`-chain. -/
theorem descRel_mono {i j : ℕ} (h : i ≤ j) : descRel hN B i ≤ descRel hN B j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (descRel_le_succ hN B _)

/-- Directedness witness for the union (any two iterates are dominated by the
later one). -/
theorem descDir (i j : ℕ) : ∃ k, (∀ X Y, (descRel hN B i).rel X Y → (descRel hN B k).rel X Y) ∧
    (∀ X Y, (descRel hN B j).rel X Y → (descRel hN B k).rel X Y) :=
  ⟨max i j, descRel_mono hN B (le_max_left i j), descRel_mono hN B (le_max_right i j)⟩

/-- **The evaluation map `val = ⋃ₙ valₙ`** as an approximable map. -/
def descMap : ApproximableMap (Exp N hN).sys B.carrier.sys :=
  iSupMap (descRel hN B) (descDir hN B)

theorem descMap_rel {A E : Set Str} :
    (descMap hN B).rel A E ↔ ∃ n, (descRel hN B n).rel A E := Iff.rfl

/-- `val` is strict (a union of strict maps). -/
theorem descMap_isStrict : IsStrict (descMap hN B) := by
  rintro Y ⟨n, hn⟩
  exact descRel_isStrict hN B n hn

/-- Directedness of the iterates in `≤`-form (for `map_continuous`). -/
theorem descDirLe (i j : ℕ) :
    ∃ k, descRel hN B i ≤ descRel hN B k ∧ descRel hN B j ≤ descRel hN B k :=
  ⟨max i j, descRel_mono hN B (le_max_left i j), descRel_mono hN B (le_max_right i j)⟩

/-- `val` is the relational union of the iterates (the hypothesis for
`map_continuous`). -/
theorem descMap_is_sup (A E : Set Str) :
    (descMap hN B).rel A E ↔ ∃ n, (descRel hN B n).rel A E := Iff.rfl

/-- **The fixed-point equation `val = k ∘ T(val) ∘ j`.** Forward: an iterate
`valₙ` is, after the
recursion, `k ∘ T(valₙ₋₁) ∘ j`, and `T(valₙ₋₁) ⊆ T(val)` by continuity on maps.
Backward: a witness
factoring through `T(valₙ)` lands in `valₙ₊₁`. -/
theorem descMap_fix :
    descMap hN B = (algStr B).comp (((Texp N).map (descMap hN B)).comp (expInv N hN)) := by
  have hmc : ∀ Y C, ((Texp N).map (descMap hN B)).rel Y C
      ↔ ∃ n, ((Texp N).map (descRel hN B n)).rel Y C :=
    fun Y C => (Texp N).map_continuous (descRel hN B) (descMap hN B) (descDirLe hN B)
      (descMap_is_sup hN B) Y C
  apply ApproximableMap.ext
  intro A E
  rw [comp_rel]
  constructor
  · rintro ⟨n, hn⟩
    have hn1 : (descRel hN B (n + 1)).rel A E := descRel_le_succ hN B n A E hn
    rw [descRel_succ, comp_rel] at hn1
    obtain ⟨C, hAC, hCE⟩ := hn1
    rw [comp_rel] at hAC
    obtain ⟨Y, hAY, hYC⟩ := hAC
    exact ⟨C, ⟨Y, hAY, (hmc Y C).mpr ⟨n, hYC⟩⟩, hCE⟩
  · rintro ⟨C, hAC, hCE⟩
    rw [comp_rel] at hAC
    obtain ⟨Y, hAY, hYC⟩ := hAC
    obtain ⟨n, hn⟩ := (hmc Y C).mp hYC
    refine ⟨n + 1, ?_⟩
    rw [descRel_succ, comp_rel]
    exact ⟨C, by rw [comp_rel]; exact ⟨Y, hAY, hn⟩, hCE⟩

/-- **The homomorphism square `val ∘ i = k ∘ T(val)`** at the raw level
(conjugating the fixed-point
equation by `i`, using `j ∘ i = I`). -/
theorem descComm :
    (descMap hN B).comp (expHom N hN) = (algStr B).comp ((Texp N).map (descMap hN B)) := by
  calc (descMap hN B).comp (expHom N hN)
      = ((algStr B).comp
          (((Texp N).map (descMap hN B)).comp (expInv N hN))).comp (expHom N hN) := by
        rw [← descMap_fix]
    _ = (algStr B).comp
        ((((Texp N).map (descMap hN B)).comp (expInv N hN)).comp (expHom N hN)) := by
        rw [comp_assoc]
    _ = (algStr B).comp
        (((Texp N).map (descMap hN B)).comp ((expInv N hN).comp (expHom N hN))) := by
        rw [comp_assoc]
    _ = (algStr B).comp (((Texp N).map (descMap hN B)).comp (idMap _)) := by
        rw [expInv_comp_expHom]
    _ = (algStr B).comp ((Texp N).map (descMap hN B)) := by rw [comp_idMap]

/-- **The evaluation homomorphism `val(s) : Exp → D`** as a `T`-algebra
homomorphism — Scott's
existence of the evaluation map. -/
def descAlgHom : AlgHom (ExpAlg N hN) B where
  hom := ⟨descMap hN B, descMap_isStrict hN B⟩
  comm := by
    apply Subtype.ext
    change (descMap hN B).comp (expHom N hN) = (algStr B).comp ((Texp N).map (descMap hN B))
    exact descComm hN B

/-- **Every homomorphism `g : Exp → D` is a fixed point** of the operator `λh. k ∘
T(h) ∘ j`.
This is
the homomorphism square `g ∘ i = k ∘ T(g)` (`g.comm`) rearranged by `i ∘ j = I`. -/
theorem algHom_fix (g : AlgHom (ExpAlg N hN) B) :
    g.hom.1 = (algStr B).comp (((Texp N).map g.hom.1).comp (expInv N hN)) := by
  have hcomm : (g.hom.1).comp (expHom N hN) = (algStr B).comp ((Texp N).map g.hom.1) :=
    congrArg Subtype.val g.comm
  calc g.hom.1
      = (g.hom.1).comp (idMap (Exp N hN).sys) := (comp_idMap _).symm
    _ = (g.hom.1).comp ((expHom N hN).comp (expInv N hN)) := by rw [expHom_comp_expInv]
    _ = ((g.hom.1).comp (expHom N hN)).comp (expInv N hN) := (comp_assoc _ _ _).symm
    _ = ((algStr B).comp ((Texp N).map g.hom.1)).comp (expInv N hN) :=
          congrArg (fun m => m.comp (expInv N hN)) hcomm
    _ = (algStr B).comp (((Texp N).map g.hom.1).comp (expInv N hN)) := comp_assoc _ _ _

/-- **`descAlgHom` is the least homomorphism**: `val ≤ g` for every homomorphism
`g : Exp → D`. The
Kleene iterates `valₙ` lie below any fixed point `g` (induction: `val₀ = ⊥ ≤ g`,
and the operator is
monotone with `g` its own fixed point), so their union `val` does too. This is the
easy half of
initiality; the matching `g ≤ val` (so `g = val`) is the projection-chain argument
of Phase 4. -/
theorem descRel_le_algHom (g : AlgHom (ExpAlg N hN) B) : ∀ n, descRel hN B n ≤ g.hom.1
  | 0 => constBot_le _
  | n + 1 => by
      rw [descRel_succ, algHom_fix hN B g]
      exact comp_mono_gen le_rfl
        (comp_mono_gen ((Texp N).map_mono (descRel_le_algHom g n)) le_rfl)

theorem descMap_le_algHom (g : AlgHom (ExpAlg N hN) B) : descMap hN B ≤ g.hom.1 := by
  intro X Y hr
  obtain ⟨n, hn⟩ := hr
  exact descRel_le_algHom hN B g n X Y hn

end Existence

/-! ## Phase 4 — uniqueness of `val(s)` and initiality of `Exp`

Scott proves homomorphisms out of the iterated colimit are unique by showing they
are *determined on
the finite elements*: the projection chain `ρₙ = iₙ ∘ jₙ` (Proposition 6.12's pair
for
`Texpⁿ({Γ}) ◁ Exp`) satisfies `T(ρₙ) = ρₙ₊₁` and `⋃ₙ ρₙ = I_Exp`, so any
homomorphism `g` equals
`⋃ₙ g ∘ ρₙ`, a sequence that is forced by the recursion (independent of `g`). The
crux is the
*concrete* "monotone on domains" content (Definition 6.13): the functor `Texp`
carries the canonical
6.12 projection pair of `D ◁ E` to that of `T(D) ◁ T(E)` — here a genuine
**equality** of maps over
`Str` (no `HEq` carrier transport, the whole point of staying in `ScottSys`).

This section establishes that crux as `GExpr.map_inj`/`GExpr.map_proj` (by
induction over the six
functor constructors), then mirrors Theorem 6.14's uniqueness argument concretely. -/

/-! ### Proposition 6.12 helpers: the projection pair is strict, and trivial on `D
◁ D` -/

/-- The injection `i : D → E` of a subsystem is **strict**: `i` sends `Δ_D` only
to `Δ_E`. -/
theorem Subsystem.inj_isStrict {α : Type*} {D E : NeighborhoodSystem α} (h : D ◁ E) :
    IsStrict h.inj := by
  intro Y hrel
  rw [Subsystem.inj_rel] at hrel
  obtain ⟨_, hYE, hsub⟩ := hrel
  exact Set.Subset.antisymm (E.sub_master hYE) (by rw [← h.master_eq]; exact hsub)

/-- The projection `j : E → D` of a subsystem is **strict**. -/
theorem Subsystem.proj_isStrict {α : Type*} {D E : NeighborhoodSystem α} (h : D ◁ E) :
    IsStrict h.proj := by
  intro X hrel
  rw [Subsystem.proj_rel] at hrel
  obtain ⟨_, hXD, hsub⟩ := hrel
  exact Set.Subset.antisymm (D.sub_master hXD) (by rw [h.master_eq]; exact hsub)

/-- On `D ◁ D` (e.g. `Subsystem.refl`), the injection is the identity (both
relations are
`X ∈ D ∧ Y ∈ D ∧ X ⊆ Y`). -/
theorem Subsystem.self_inj {α : Type*} {D : NeighborhoodSystem α} (h : D ◁ D) :
    h.inj = idMap D := by
  apply ApproximableMap.ext
  intro X Y
  rw [Subsystem.inj_rel, idMap_rel]

/-- On `D ◁ D`, the projection is the identity. -/
theorem Subsystem.self_proj {α : Type*} {D : NeighborhoodSystem α} (h : D ◁ D) :
    h.proj = idMap D := by
  apply ApproximableMap.ext
  intro X Y
  rw [Subsystem.proj_rel, idMap_rel]

/-! ### The functor carries projection pairs: the token-level lemmas -/

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **Sum carries the injection.** `(i₀ + i₁) = i` for the sum subsystem: both
relate `W ↦ W'` iff
`W ∈ 𝒟₀+𝒟₁`, `W' ∈ ℰ₀+ℰ₁`, `W ⊆ W'`. -/
theorem sumMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    sumMapTok h0.inj h1.inj = (sumTok_subsystem h0 h1).inj := by
  have hsubM : ∀ {W : Set Str}, (A₀.sum A₁).sys.mem W → W ⊆ sumTokMaster B₀.sys B₁.sys := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact (show sumTokMaster A₀.sys A₁.sys = sumTokMaster B₀.sys B₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact embF_subset_sumTokMaster (h0.sub hX)
    · exact embT_subset_sumTokMaster (h1.sub hY)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXsub⟩, rfl, rfl⟩ | ⟨Y, Y', ⟨hY, hY', hYsub⟩, rfl, rfl⟩)
    · exact ⟨hW, (B₀.sum B₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨X', hX', rfl⟩), embBit_subset.mpr hXsub⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨Y', hY', rfl⟩), embBit_subset.mpr hYsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, rfl, rfl⟩)

/-- **Sum carries the projection.** -/
theorem sumMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    sumMapTok h0.proj h1.proj = (sumTok_subsystem h0 h1).proj := by
  have hsubM : ∀ {W : Set Str}, (B₀.sum B₁).sys.mem W → W ⊆ sumTokMaster A₀.sys A₁.sys := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact (show sumTokMaster B₀.sys B₁.sys = sumTokMaster A₀.sys A₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact (embBit_subset.mpr (by rw [h0.master_eq]; exact B₀.sys.sub_master hX)).trans
        (embF_subset_sumTokMaster A₀.sys.master_mem)
    · exact (embBit_subset.mpr (by rw [h1.master_eq]; exact B₁.sys.sub_master hY)).trans
        (embT_subset_sumTokMaster A₁.sys.master_mem)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXsub⟩, rfl, rfl⟩ | ⟨Y, Y', ⟨hY, hY', hYsub⟩, rfl, rfl⟩)
    · exact ⟨hW, (A₀.sum A₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨X', hX', rfl⟩), embBit_subset.mpr hXsub⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨Y', hY', rfl⟩), embBit_subset.mpr hYsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, rfl, rfl⟩)

/-- **Product carries the injection.** -/
theorem prodMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    prodMapTok h0.inj h1.inj = (prodTok_subsystem h0 h1).inj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩
    exact ⟨prodTok_mem_prodTokNbhd hX hY, prodTok_mem_prodTokNbhd hX' hY',
      prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨⟨X, Y, hX, hY, rfl⟩, ⟨X', Y', hX', hY', rfl⟩, hsub⟩
    obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩

/-- **Product carries the projection.** -/
theorem prodMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    prodMapTok h0.proj h1.proj = (prodTok_subsystem h0 h1).proj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩
    exact ⟨prodTok_mem_prodTokNbhd hX hY, prodTok_mem_prodTokNbhd hX' hY',
      prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨⟨X, Y, hX, hY, rfl⟩, ⟨X', Y', hX', hY', rfl⟩, hsub⟩
    obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩

/-- **Coalesced sum carries the injection.** -/
theorem oplusMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    oplusMapTok h0.inj h1.inj = (oplusTok_subsystem h0 h1).inj := by
  have hsubM : ∀ {W : Set Str}, (A₀.oplus A₁).sys.mem W → W ⊆ sumTokMaster B₀.sys B₁.sys := by
    rintro W (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
    · exact (show sumTokMaster A₀.sys A₁.sys = sumTokMaster B₀.sys B₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact embF_subset_sumTokMaster (h0.sub hX)
    · exact embT_subset_sumTokMaster (h1.sub hY)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXs⟩, hXne, hX'ne, rfl, rfl⟩ |
      ⟨Y, Y', ⟨hY, hY', hYs⟩, hYne, hY'ne, rfl, rfl⟩)
    · exact ⟨hW, (B₀.oplus B₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩), Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩),
        embBit_subset.mpr hXs⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩), Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩),
        embBit_subset.mpr hYs⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, hXne, hX'ne, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, hYne, hY'ne, rfl, rfl⟩)

/-- **Coalesced sum carries the projection.** -/
theorem oplusMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    oplusMapTok h0.proj h1.proj = (oplusTok_subsystem h0 h1).proj := by
  have hsubM : ∀ {W : Set Str}, (B₀.oplus B₁).sys.mem W → W ⊆ sumTokMaster A₀.sys A₁.sys := by
    rintro W (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
    · exact (show sumTokMaster B₀.sys B₁.sys = sumTokMaster A₀.sys A₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact (embBit_subset.mpr (by rw [h0.master_eq]; exact B₀.sys.sub_master hX)).trans
        (embF_subset_sumTokMaster A₀.sys.master_mem)
    · exact (embBit_subset.mpr (by rw [h1.master_eq]; exact B₁.sys.sub_master hY)).trans
        (embT_subset_sumTokMaster A₁.sys.master_mem)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXs⟩, hXne, hX'ne, rfl, rfl⟩ |
      ⟨Y, Y', ⟨hY, hY', hYs⟩, hYne, hY'ne, rfl, rfl⟩)
    · exact ⟨hW, (A₀.oplus A₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩), Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩),
        embBit_subset.mpr hXs⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩), Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩),
        embBit_subset.mpr hYs⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, hXne, hX'ne, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, hYne, hY'ne, rfl, rfl⟩)

/-- **Smash product carries the injection.** -/
theorem otimesMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    otimesMapTok h0.inj h1.inj = (otimesTok_subsystem h0 h1).inj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ |
      ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩)
    · refine ⟨hW, (B₀.otimes B₁).sys.master_mem, ?_⟩
      rcases hW with rfl | ⟨P, Q, hP, hQ, hPne, hQne, rfl⟩
      · exact (show prodTokNbhd A₀.sys.master A₁.sys.master
            = prodTokNbhd B₀.sys.master B₁.sys.master by rw [h0.master_eq, h1.master_eq]).subset
      · exact prodTokNbhd_subset_iff.mpr ⟨B₀.sys.sub_master (h0.sub hP),
          B₁.sys.sub_master (h1.sub hQ)⟩
    · exact ⟨Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩, Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩,
        prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · obtain ⟨hsX, _⟩ := prodTokNbhd_subset_iff.mp hsub
        exact absurd (Set.Subset.antisymm (B₀.sys.sub_master hX')
          (by rw [← h0.master_eq]; exact hsX)) hX'ne
      · obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
        exact Or.inr ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩,
          hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩

/-- **Smash product carries the projection.** -/
theorem otimesMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    otimesMapTok h0.proj h1.proj = (otimesTok_subsystem h0 h1).proj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ |
      ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩)
    · refine ⟨hW, (A₀.otimes A₁).sys.master_mem, ?_⟩
      rcases hW with rfl | ⟨P, Q, hP, hQ, hPne, hQne, rfl⟩
      · exact (show prodTokNbhd B₀.sys.master B₁.sys.master
            = prodTokNbhd A₀.sys.master A₁.sys.master by rw [h0.master_eq, h1.master_eq]).subset
      · exact prodTokNbhd_subset_iff.mpr ⟨by rw [h0.master_eq]; exact B₀.sys.sub_master hP,
          by rw [h1.master_eq]; exact B₁.sys.sub_master hQ⟩
    · exact ⟨Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩, Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩,
        prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · obtain ⟨hsX, _⟩ := prodTokNbhd_subset_iff.mp hsub
        exact absurd (Set.Subset.antisymm (A₀.sys.sub_master hX')
          (by rw [h0.master_eq]; exact hsX)) hX'ne
      · obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
        exact Or.inr ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩,
          hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩

/-! ### The crux (Definition 6.13, concrete): `T` carries the 6.12 projection pair

This is the *monotone on domains* content of Definition 6.13, but here a genuine
**equality** of maps
over the single token type `Str` (no `HEq` carrier transport): the functor `T =
GExpr` sends the
injection/projection of `D ◁ E` to the injection/projection of `T(D) ◁ T(E)`.
Proved by induction
over the six constructors using the token-level lemmas just established. -/

/-- **`T(i) = i'`** — the functor carries the injection of `D ◁ E` to that of
`T(D) ◁ T(E)`. -/
theorem GExpr.map_inj : (T : GExpr) → {X Y : ScottSys} → (h : X.sys ◁ Y.sys) →
    T.map h.inj = (T.obj_subsystem h).inj
  | .const D, _, _, _ => (Subsystem.self_inj (Subsystem.refl D.sys)).symm
  | .var, _, _, _ => rfl
  | .sum a b, _, _, h => by
      change sumMapTok (a.map h.inj) (b.map h.inj)
          = (sumTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, sumMapTok_inj]
  | .prod a b, _, _, h => by
      change prodMapTok (a.map h.inj) (b.map h.inj)
          = (prodTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, prodMapTok_inj]
  | .oplus a b, _, _, h => by
      change oplusMapTok (a.map h.inj) (b.map h.inj)
          = (oplusTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, oplusMapTok_inj]
  | .otimes a b, _, _, h => by
      change otimesMapTok (a.map h.inj) (b.map h.inj)
          = (otimesTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, otimesMapTok_inj]

/-- **`T(j) = j'`** — the functor carries the projection of `D ◁ E` to that of
`T(D) ◁ T(E)`. -/
theorem GExpr.map_proj : (T : GExpr) → {X Y : ScottSys} → (h : X.sys ◁ Y.sys) →
    T.map h.proj = (T.obj_subsystem h).proj
  | .const D, _, _, _ => (Subsystem.self_proj (Subsystem.refl D.sys)).symm
  | .var, _, _, _ => rfl
  | .sum a b, _, _, h => by
      change sumMapTok (a.map h.proj) (b.map h.proj)
          = (sumTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, sumMapTok_proj]
  | .prod a b, _, _, h => by
      change prodMapTok (a.map h.proj) (b.map h.proj)
          = (prodTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, prodMapTok_proj]
  | .oplus a b, _, _, h => by
      change oplusMapTok (a.map h.proj) (b.map h.proj)
          = (oplusTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, oplusMapTok_proj]
  | .otimes a b, _, _, h => by
      change otimesMapTok (a.map h.proj) (b.map h.proj)
          = (otimesTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, otimesMapTok_proj]

/-! ### The identity structure isomorphism, relationally -/

/-- The forward map of the identity iso `isoOfObjEq e` is the inclusion `X ↪ Y` (=
`idMap`
across the
object equality `e`). -/
theorem isoOfObjEq_hom_rel {X Y : ScottSys} (e : X = Y) {A E : Set Str} :
    ((isoOfObjEq e).hom).1.rel A E ↔ X.sys.mem A ∧ Y.sys.mem E ∧ A ⊆ E := by
  cases e; exact idMap_rel

/-- The inverse map of the identity iso `isoOfObjEq e`. -/
theorem isoOfObjEq_inv_rel {X Y : ScottSys} (e : X = Y) {A E : Set Str} :
    ((isoOfObjEq e).inv).1.rel A E ↔ Y.sys.mem A ∧ X.sys.mem E ∧ A ⊆ E := by
  cases e; exact idMap_rel

/-- **Relational description of the structure map `i = expHom`** (the identity
`T(Exp) = Exp`). -/
theorem expHom_rel {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) {A E : Set Str} :
    (expHom N hN).rel A E ↔
      ((Texp N).obj (Exp N hN)).sys.mem A ∧ (Exp N hN).sys.mem E ∧ A ⊆ E :=
  isoOfObjEq_hom_rel (Exp_structure_eq N hN)

/-- **Relational description of the inverse structure map `j = expInv`**. -/
theorem expInv_rel {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) {A E : Set Str} :
    (expInv N hN).rel A E ↔
      (Exp N hN).sys.mem A ∧ ((Texp N).obj (Exp N hN)).sys.mem E ∧ A ⊆ E :=
  isoOfObjEq_inv_rel (Exp_structure_eq N hN)

/-! ### The projection chain `ρₙ = iₙ ∘ jₙ` and `⋃ₙ ρₙ = I_Exp` -/

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

/-- The subdomain `Texpⁿ({Γ}) ◁ Exp` (Proposition 6.12's pair lives here). -/
theorem expSub (n : ℕ) : (gTower (Texp N) n).sys ◁ (Exp N hN).sys :=
  gTower_sub_colim (Texp N) (Texp_rooted hN) n

/-- **`ρₙ = iₙ ∘ jₙ : Exp → Exp`**, the retraction onto `Texpⁿ({Γ})`. -/
def rho (n : ℕ) : ApproximableMap (Exp N hN).sys (Exp N hN).sys :=
  (expSub hN n).inj.comp (expSub hN n).proj

/-- Scott's relational description `A ρₙ E ↔ ∃ z ∈ Texpⁿ({Γ}), A ⊆ z ⊆ E`. -/
theorem rho_rel (n : ℕ) {A E : Set Str} :
    (rho hN n).rel A E ↔ (Exp N hN).sys.mem A ∧ (Exp N hN).sys.mem E ∧
      ∃ z, (gTower (Texp N) n).sys.mem z ∧ A ⊆ z ∧ z ⊆ E := by
  unfold rho
  rw [comp_rel]
  constructor
  · rintro ⟨z, hproj, hinj⟩
    rw [Subsystem.proj_rel] at hproj
    rw [Subsystem.inj_rel] at hinj
    obtain ⟨hcA, hTz, hAz⟩ := hproj
    obtain ⟨_, hcE, hzE⟩ := hinj
    exact ⟨hcA, hcE, z, hTz, hAz, hzE⟩
  · rintro ⟨hcA, hcE, z, hTz, hAz, hzE⟩
    exact ⟨z, by rw [Subsystem.proj_rel]; exact ⟨hcA, hTz, hAz⟩,
      by rw [Subsystem.inj_rel]; exact ⟨hTz, hcE, hzE⟩⟩

/-- `ρₙ ⊆ ρₘ` for `n ≤ m`. -/
theorem rho_mono {n m : ℕ} (h : n ≤ m) {A E : Set Str} (hr : (rho hN n).rel A E) :
    (rho hN m).rel A E := by
  rw [rho_rel] at hr ⊢
  obtain ⟨hcA, hcE, z, hTz, hAz, hzE⟩ := hr
  exact ⟨hcA, hcE, z, (gTower_le (Texp N) (Texp_rooted hN) h).sub hTz, hAz, hzE⟩

/-- The pointwise union `⋃ₙ ρₙ`. -/
def iSupRho : ApproximableMap (Exp N hN).sys (Exp N hN).sys :=
  iSupMap (rho hN) (fun i j => ⟨max i j,
    fun _ _ h => rho_mono hN (le_max_left i j) h,
    fun _ _ h => rho_mono hN (le_max_right i j) h⟩)

/-- **`⋃ₙ ρₙ = I_Exp`** (Scott's key identity). -/
theorem iSupRho_eq_id : iSupRho hN = idMap (Exp N hN).sys := by
  apply ApproximableMap.ext
  intro A E
  rw [idMap_rel]
  constructor
  · rintro ⟨n, hr⟩
    rw [rho_rel] at hr
    obtain ⟨hcA, hcE, z, _, hAz, hzE⟩ := hr
    exact ⟨hcA, hcE, hAz.trans hzE⟩
  · rintro ⟨hcA, hcE, hAE⟩
    obtain ⟨n, hA⟩ := hcA
    exact ⟨n, (rho_rel hN n).mpr ⟨⟨n, hA⟩, hcE, A, hA, subset_rfl, hAE⟩⟩

/-- **`ρ₀ = ⊥`** (the generator `{Γ}` is one-point): `ρ₀` relates `A` only to the
master. -/
theorem rho_zero_rel {A E : Set Str} :
    (rho hN 0).rel A E ↔ (Exp N hN).sys.mem A ∧ E = (Exp N hN).sys.master := by
  rw [rho_rel]
  constructor
  · rintro ⟨hcA, hcE, z, hz, _, hzE⟩
    have hzm : z = (Exp N hN).sys.master :=
      (hz : z = gFix (Texp N)).trans (gColim_master (Texp N) (Texp_rooted hN)).symm
    subst hzm
    exact ⟨hcA, Set.Subset.antisymm ((Exp N hN).sys.sub_master hcE) hzE⟩
  · rintro ⟨hcA, rfl⟩
    exact ⟨hcA, (Exp N hN).sys.master_mem, (Exp N hN).sys.master,
      gColim_master (Texp N) (Texp_rooted hN), (Exp N hN).sys.sub_master hcA, subset_rfl⟩

/-! ### The crux equation `ρₙ₊₁ = i ∘ T(ρₙ) ∘ j` -/

/-- `T(ρₙ) = T(iₙ) ∘ T(jₙ) = i'ₙ ∘ j'ₙ`, the projection pair of `T(Texpⁿ{Γ}) ◁
T(Exp)`. -/
theorem map_rho_eq (n : ℕ) :
    (Texp N).map (rho hN n)
      = ((Texp N).obj_subsystem (expSub hN n)).inj.comp
        ((Texp N).obj_subsystem (expSub hN n)).proj := by
  unfold rho
  rw [(Texp N).map_comp (expSub hN n).proj (Subsystem.inj_isStrict (expSub hN n)),
      (Texp N).map_inj, (Texp N).map_proj]

/-- **`ρₙ₊₁ = i ∘ T(ρₙ) ∘ j`** (Scott's `T(ρₙ) = ρₙ₊₁`, conjugated by the
structure iso). -/
theorem key_rho (n : ℕ) :
    rho hN (n + 1)
      = (expHom N hN).comp (((Texp N).map (rho hN n)).comp (expInv N hN)) := by
  have hsyseq : ((Texp N).obj (Exp N hN)).sys = (Exp N hN).sys :=
    gColim_obj_sys_eq (Texp N) (Texp_rooted hN)
  apply ApproximableMap.ext
  intro A E
  rw [map_rho_eq]
  simp only [comp_rel, rho_rel, expInv_rel, expHom_rel, Subsystem.proj_rel,
    Subsystem.inj_rel, hsyseq]
  constructor
  · rintro ⟨hcA, hcE, z, hTz, hAz, hzE⟩
    exact ⟨E, ⟨A, ⟨hcA, hcA, subset_rfl⟩, z, ⟨hcA, hTz, hAz⟩, hTz, hcE, hzE⟩,
      hcE, hcE, subset_rfl⟩
  · rintro ⟨Y, ⟨C, ⟨hcA, _, hAC⟩, z, ⟨_, hTz, hCz⟩, _, _, hzY⟩, _, hcE, hYE⟩
    exact ⟨hcA, hcE, z, hTz, hAC.trans hCz, hzY.trans hYE⟩

/-! ### `g`-independence of `g ∘ ρₙ` and uniqueness -/

variable (B : TAlgebra (TexpF N))

/-- The base of the recursion: `g ∘ ρ₀ = ⊥ = val₀`, independent of `g`. -/
theorem gcomp_rho_zero (g : AlgHom (ExpAlg N hN) B) :
    g.hom.1.comp (rho hN 0) = descRel hN B 0 := by
  apply ApproximableMap.ext
  intro A Z
  rw [comp_rel]
  constructor
  · rintro ⟨E, hrho, hg⟩
    rw [rho_zero_rel] at hrho
    obtain ⟨hcA, rfl⟩ := hrho
    have hZ : Z = B.carrier.sys.master := g.hom.2 hg
    exact ⟨hcA, by rw [NeighborhoodSystem.mem_bot]; exact hZ⟩
  · rintro ⟨hcA, hZ⟩
    rw [NeighborhoodSystem.mem_bot] at hZ
    subst hZ
    exact ⟨(Exp N hN).sys.master, (rho_zero_rel hN).mpr ⟨hcA, rfl⟩, g.hom.1.master_rel⟩

/-- **The fixed-point recursion `gₙ₊₁ = k ∘ T(gₙ) ∘ j`** (`key_rho` + the
homomorphism square). -/
theorem gcomp_rho_succ (g : AlgHom (ExpAlg N hN) B) (n : ℕ) :
    g.hom.1.comp (rho hN (n + 1))
      = (algStr B).comp (((Texp N).map (g.hom.1.comp (rho hN n))).comp (expInv N hN)) := by
  have hcomm : (g.hom.1).comp (expHom N hN) = (algStr B).comp ((Texp N).map g.hom.1) :=
    congrArg Subtype.val g.comm
  calc g.hom.1.comp (rho hN (n + 1))
      = g.hom.1.comp ((expHom N hN).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN))) := by rw [key_rho]
    _ = (g.hom.1.comp (expHom N hN)).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN)) :=
        (comp_assoc _ _ _).symm
    _ = ((algStr B).comp ((Texp N).map g.hom.1)).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN)) :=
        congrArg (fun m => m.comp (((Texp N).map (rho hN n)).comp (expInv N hN))) hcomm
    _ = (algStr B).comp (((Texp N).map g.hom.1).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN))) := comp_assoc _ _ _
    _ = (algStr B).comp ((((Texp N).map g.hom.1).comp ((Texp N).map (rho hN n))).comp
          (expInv N hN)) :=
        congrArg ((algStr B).comp ·)
          (comp_assoc ((Texp N).map g.hom.1) ((Texp N).map (rho hN n)) (expInv N hN)).symm
    _ = (algStr B).comp (((Texp N).map (g.hom.1.comp (rho hN n))).comp (expInv N hN)) :=
        congrArg (fun m => (algStr B).comp (m.comp (expInv N hN)))
          ((Texp N).map_comp (rho hN n) g.hom.2).symm

/-- **`g ∘ ρₙ = val₀ₙ`**: every homomorphism `g` agrees with the canonical Kleene
iterate after the
`n`-th projection — the sequence is forced by the recursion, independent of `g`. -/
theorem gcomp_rho_eq (g : AlgHom (ExpAlg N hN) B) :
    ∀ n, g.hom.1.comp (rho hN n) = descRel hN B n
  | 0 => gcomp_rho_zero hN B g
  | n + 1 => by rw [gcomp_rho_succ hN B g n, gcomp_rho_eq g n, ← descRel_succ]

/-- **The underlying map of any homomorphism `g : Exp → D` is `val = descMap`.**
Hence `descAlgHom`
is the *unique* homomorphism. -/
theorem descMap_eq_algHom (g : AlgHom (ExpAlg N hN) B) : g.hom.1 = descMap hN B := by
  have hcomp : g.hom.1.comp (iSupRho hN) = descMap hN B := by
    apply ApproximableMap.ext
    intro A E
    rw [comp_rel, descMap_rel]
    constructor
    · rintro ⟨Y, ⟨n, hrho⟩, hg⟩
      refine ⟨n, ?_⟩
      rw [← gcomp_rho_eq hN B g n, comp_rel]
      exact ⟨Y, hrho, hg⟩
    · rintro ⟨n, hn⟩
      rw [← gcomp_rho_eq hN B g n, comp_rel] at hn
      obtain ⟨Y, hrho, hg⟩ := hn
      exact ⟨Y, ⟨n, hrho⟩, hg⟩
  calc g.hom.1 = g.hom.1.comp (iSupRho hN) := by
        rw [iSupRho_eq_id hN]; exact (comp_idMap g.hom.1).symm
    _ = descMap hN B := hcomp

/-- Two algebra homomorphisms with equal underlying maps are equal. -/
theorem algHom_ext {A C : TAlgebra (TexpF N)} {g g' : AlgHom A C} (h : g.hom = g'.hom) :
  g = g' := by
  cases g; cases g'; cases h; rfl

/-- **Exercise 6.23 (Scott 1981, PRG-19) — `Exp` is the initial `T`-algebra.** For
every algebra
`B = (D, s, u, v)` there is a *unique* homomorphism `val(s) : Exp → D` — Scott's
evaluation of an
expression. Existence is `descAlgHom` (Phase 3); uniqueness is the
projection-chain argument. -/
def ExpInitial : IsInitial (ExpAlg N hN) where
  desc B := descAlgHom hN B
  uniq B g := algHom_ext (Subtype.ext (descMap_eq_algHom hN B g))

end Uniqueness

end Exercise619

end Domain.Neighborhood
