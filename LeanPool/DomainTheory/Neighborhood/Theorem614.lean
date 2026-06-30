/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Definition613
import LeanPool.DomainTheory.Neighborhood.Theorem69
import LeanPool.DomainTheory.Neighborhood.ApproximableExercises

/-!
# Lecture VI — Theorem 6.14 (Scott 1981, PRG-19): existence of initial
`T`-algebras

> **THEOREM 6.14.** If the functor `T` is continuous on maps and monotone and
continuous on domains,
> and if there is a set `Γ` such that `{Γ} ◁ T({Γ})`, then there exists an initial
`T`-algebra.

Scott's proof iterates the functor from the generating system `{Γ}`. The
assumption
`{Γ} ◁ T({Γ})` means `T({Γ})` is a system over the same token set `Γ`; iterating,
every
`Tⁿ({Γ})` is over `Γ` and `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ})`. The colimit

`𝒟 = ⋃ₙ Tⁿ({Γ})`

is then a system over `Γ` with `Tⁿ({Γ}) ◁ 𝒟`, whence `𝒟 ◁ T(𝒟)`, and *continuity
on domains*
gives `T(𝒟) = 𝒟` — the isomorphism `𝒟 ≅ T(𝒟)` is the **identity**. So `𝒟` is a
`T`-algebra, and:

* **existence** of homomorphisms out of `𝒟` is Theorem 6.9
(`nonempty_algHom_of_continuousOnMaps`);
* **uniqueness** is the `ρₙ = iₙ ∘ jₙ` projection-chain argument: `T(ρₙ) = ρₙ₊₁`
(monotone on
  domains), `⋃ₙ ρₙ = I_𝒟`, and any homomorphism `h` is `⋃ₙ h∘ρₙ`, the least fixed
  point of
  `λh. k ∘ T(h)`.

## The carrier-type subtlety

The abstract `T : Endofunctor DomainObj` need not preserve token types, so
`Tⁿ({Γ})` a priori live
over different carriers. The hypothesis `{Γ} ◁ T({Γ})` already pins `T({Γ})` to
`Γ`'s carrier, and
*monotone on domains* (Definition 6.13, `MonotoneAt.carrier_eq`) propagates the
identification up the
tower. We carry the carrier equalities explicitly and transport along them; the
transport of the
subdomain relation is the choice-free `subsystem_cast`.

## Lean note: `rw` fragility on defeq-but-not-syntactic implicits

Throughout the uniqueness half, `rw` with explicit arguments at the
`ApproximableMap` /
`NeighborhoodSystem` level repeatedly failed with "did not find an occurrence of
the pattern" even
when the pattern was visibly present — because the implicit carriers/systems were
**defeq but not
syntactically equal** (`colim s` vs `(colimAlg s).carrier.sys` vs `(objColim
s).sys`; the abbrev
`objColim` vs the literal `⟨Tok, colim s⟩`). Three fixes, used throughout
`gcomp_rho_succ`/`gcomp_eq`:
* work at the categorical `⊚` / `Category.assoc` level, where the implicits are
concrete `DomainObj`s
  rather than systems, so unification has nothing to get stuck on;
* prefer `congrArg` / `calc` **term-mode** proofs (e.g. `congrArg (fun x => g.hom
⊚ x) (key_rho s n)`),
  since `calc` bridges adjacent steps by defeq rather than by syntactic match;
* to rewrite with a lemma whose implicit is pinned to the "wrong" representation
(e.g. `comp_idMap`,
  whose `idMap` arg is tied to `g.hom`'s domain `(colimAlg s).carrier.sys`), first
  bind the fact via a
  `have` stated in the *desired* form (`have e : g.hom.comp (idMap (colim s)) =
  g.hom := comp_idMap
  g.hom` — the `have` unifies by defeq), then `rw [← e]`.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap Domain.Neighborhood.Exercise510

universe w

namespace Theorem614

/-! ### Carrier-transport helpers -/

variable {α : Type w}

/-- Transport a subsystem relation `D ◁ E` along a carrier-type equality `β = α`.
Choice-free. -/
theorem subsystem_cast {β : Type w} (e : β = α) {D E : NeighborhoodSystem β} (h : D ◁ E) :
    (e ▸ D : NeighborhoodSystem α) ◁ (e ▸ E : NeighborhoodSystem α) := by
  cases e; exact h

/-- Transport composition for neighbourhood systems: `e' ▸ (e ▸ x) = (e.trans e')
▸ x`. -/
theorem rec_trans {β γ : Type w} (e : β = γ) (e' : γ = α) (x : NeighborhoodSystem β) :
    (e' ▸ (e ▸ x : NeighborhoodSystem γ) : NeighborhoodSystem α) = (e.trans e') ▸ x := by
  cases e; cases e'; rfl

/-- Membership in a transported system: `(e ▸ V).mem X ↔ V.mem (e.symm ▸ X)`. -/
theorem mem_cast {β : Type w} (e : β = α) (V : NeighborhoodSystem β) (X : Set α) :
    (e ▸ V : NeighborhoodSystem α).mem X ↔ V.mem (e.symm ▸ X : Set β) := by
  cases e; rfl

/-- Transport composition for sets: `e' ▸ (e ▸ X) = (e.trans e') ▸ X`. -/
theorem set_rec_trans {β γ : Type w} (e : β = γ) (e' : γ = α) (X : Set β) :
    (e' ▸ (e ▸ X : Set γ) : Set α) = (e.trans e') ▸ X := by
  cases e; cases e'; rfl

/-! ### The setup bundle (hypotheses of Theorem 6.14) -/

/-- The hypotheses of Theorem 6.14, bundled: a functor `T` that is continuous on
maps, monotone and
continuous on domains, together with a generating system `Γ` over a token type
`Tok` such that
`{Γ} ◁ T({Γ})` (the carrier of `T({Γ})` is identified with `Tok` by `ceq`, and
`hsub` is Scott's
`{Γ} ◁ T({Γ})`). -/
structure Setup where
  /-- The functor. -/
  T : Endofunctor DomainObj.{w}
  /-- `T` is continuous on maps (Definition 6.8). -/
  hmaps : ContinuousOnMaps T
  /-- `T` is monotone on domains (Definition 6.13). -/
  hmono : MonotoneOnDomains T
  /-- `T` is continuous on domains (Definition 6.13). -/
  hcont : ContinuousOnDomains T
  /-- The token type of the generating system. -/
  {Tok : Type w}
  /-- The generating system `{Γ}`. -/
  Γ : NeighborhoodSystem Tok
  /-- `T({Γ})` is a system over the same token type. -/
  ceq : (T.obj ⟨Tok, Γ⟩).carrier = Tok
  /-- Scott's hypothesis `{Γ} ◁ T({Γ})`. -/
  hsub : Γ ◁ (ceq ▸ (T.obj ⟨Tok, Γ⟩).sys : NeighborhoodSystem Tok)

/-! ### The iterated functor tower `Tⁿ({Γ})` -/

/-- The iterated tower, as data: at level `n`, the system `Tⁿ({Γ})` over `Tok`,
the carrier
identification `(T.obj Tⁿ({Γ})).carrier = Tok`, and the subdomain relation
`Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ})`
(where `Tⁿ⁺¹({Γ})` is the carrier-transport of `T(Tⁿ({Γ}))`). The successor step
uses
*monotone on domains* (`MonotoneAt`) to obtain the next carrier identification and
subdomain
relation. Choice-free. -/
def iter (s : Setup.{w}) : (n : ℕ) →
    Σ' (S : NeighborhoodSystem s.Tok), Σ' (ceq : (s.T.obj ⟨s.Tok, S⟩).carrier = s.Tok),
      S ◁ (ceq ▸ (s.T.obj ⟨s.Tok, S⟩).sys : NeighborhoodSystem s.Tok)
  | 0 => ⟨s.Γ, s.ceq, s.hsub⟩
  | (n + 1) =>
      let p := iter s n
      ⟨p.2.1 ▸ (s.T.obj ⟨s.Tok, p.1⟩).sys,
        (s.hmono p.2.2).carrier_eq.trans p.2.1,
        by
          have hsub := subsystem_cast p.2.1 (s.hmono p.2.2).sub
          rwa [rec_trans] at hsub⟩

/-- `Tⁿ({Γ})`, the `n`-th system in the tower (over `Tok`). -/
def Dsys (s : Setup.{w}) (n : ℕ) : NeighborhoodSystem s.Tok := (iter s n).1

/-- The carrier identification `(T.obj Tⁿ({Γ})).carrier = Tok`. -/
theorem Dceq (s : Setup.{w}) (n : ℕ) : (s.T.obj ⟨s.Tok, Dsys s n⟩).carrier = s.Tok :=
  (iter s n).2.1

/-- `Tⁿ⁺¹({Γ})` is the carrier-transport of `T(Tⁿ({Γ}))`. -/
theorem Dsys_succ (s : Setup.{w}) (n : ℕ) :
    Dsys s (n + 1) = (Dceq s n ▸ (s.T.obj ⟨s.Tok, Dsys s n⟩).sys : NeighborhoodSystem s.Tok) :=
  rfl

/-- The basic subdomain step `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ})`. -/
theorem Dchain (s : Setup.{w}) (n : ℕ) : Dsys s n ◁ Dsys s (n + 1) := (iter s n).2.2

/-- Every system in the tower has the same master `Δ = Γ`. -/
theorem Dsys_master (s : Setup.{w}) (n : ℕ) : (Dsys s n).master = s.Γ.master := by
  induction n with
  | zero => rfl
  | succ k ih => rw [← (Dchain s k).master_eq]; exact ih

/-- The tower is a `◁`-chain: `Tⁿ({Γ}) ◁ Tᵐ({Γ})` whenever `n ≤ m`. -/
theorem chain_le (s : Setup.{w}) {n m : ℕ} (h : n ≤ m) : Dsys s n ◁ Dsys s m := by
  induction h with
  | refl => exact Subsystem.refl _
  | step _ ih => exact ih.trans (Dchain s _)

/-! ### The colimit `𝒟 = ⋃ₙ Tⁿ({Γ})` -/

/-- **The colimit `𝒟 = ⋃ₙ Tⁿ({Γ})`** as a neighbourhood system over `Tok`: a set
is a neighbourhood
of `𝒟` exactly when it is a neighbourhood of some `Tⁿ({Γ})`. Closure under
consistent intersection
uses that the tower is a chain (`chain_le`): any finite collection of
neighbourhoods sits inside one
level `Tᴺ({Γ})`, whose own `inter_mem` finishes the job. -/
def colim (s : Setup.{w}) : NeighborhoodSystem s.Tok where
  mem X := ∃ n, (Dsys s n).mem X
  master := s.Γ.master
  master_mem := ⟨0, s.Γ.master_mem⟩
  inter_mem := by
    rintro X Y Z ⟨n, hX⟩ ⟨m, hY⟩ ⟨p, hZ⟩ hsub
    set N := max n (max m p) with hN
    have hXN : (Dsys s N).mem X := (chain_le s (le_max_left n _)).sub hX
    have hYN : (Dsys s N).mem Y :=
      (chain_le s ((le_max_left m p).trans (le_max_right n _))).sub hY
    have hZN : (Dsys s N).mem Z :=
      (chain_le s ((le_max_right m p).trans (le_max_right n _))).sub hZ
    exact ⟨N, (Dsys s N).inter_mem hXN hYN hZN hsub⟩
  sub_master := by
    rintro X ⟨n, hX⟩
    rw [← Dsys_master s n]
    exact (Dsys s n).sub_master hX

@[simp] theorem mem_colim (s : Setup.{w}) {X : Set s.Tok} :
    (colim s).mem X ↔ ∃ n, (Dsys s n).mem X := Iff.rfl

@[simp] theorem colim_master (s : Setup.{w}) : (colim s).master = s.Γ.master := rfl

/-- Each level of the tower is a subdomain of the colimit: `Tⁿ({Γ}) ◁ 𝒟`. -/
theorem Dsys_sub_colim (s : Setup.{w}) (n : ℕ) : Dsys s n ◁ colim s where
  master_eq := by rw [colim_master, Dsys_master]
  sub hX := ⟨n, hX⟩
  inter_closed := by
    rintro X Y hX hY ⟨m, hXY⟩
    have hN : (Dsys s (max n m)).mem (X ∩ Y) := by
      have hle : (Dsys s m) ◁ (Dsys s (max n m)) := chain_le s (le_max_right n m)
      exact hle.sub hXY
    -- pull `X ∩ Y` back into `Tⁿ({Γ})` using consistency-in-the-bigger-level
    exact (chain_le s (le_max_left n m)).inter_closed hX hY hN

/-! ### `T(𝒟)` and the relation `𝒟 ◁ T(𝒟)` -/

/-- The carrier identification `(T.obj 𝒟).carrier = Tok`, from `MonotoneAt` of
`T⁰({Γ}) ◁ 𝒟`. -/
theorem colimCeq (s : Setup.{w}) : (s.T.obj ⟨s.Tok, colim s⟩).carrier = s.Tok :=
  (s.hmono (Dsys_sub_colim s 0)).carrier_eq.trans (Dceq s 0)

/-- `T(𝒟)`, the image of the colimit, as a system over `Tok` (via `colimCeq`). -/
def Tcolim (s : Setup.{w}) : NeighborhoodSystem s.Tok :=
  colimCeq s ▸ (s.T.obj ⟨s.Tok, colim s⟩).sys

/-- `Tⁿ⁺¹({Γ}) ◁ T(𝒟)`: applying *monotone on domains* to `Tⁿ({Γ}) ◁ 𝒟` and
transporting. -/
theorem Dsys_sub_Tcolim (s : Setup.{w}) (n : ℕ) : Dsys s (n + 1) ◁ Tcolim s := by
  have h := subsystem_cast (Dceq s n) (s.hmono (Dsys_sub_colim s n)).sub
  rw [rec_trans] at h
  exact h

/-- `T(𝒟)` and `𝒟` share the master `Δ = Γ`. -/
theorem Tcolim_master (s : Setup.{w}) : (Tcolim s).master = s.Γ.master := by
  rw [← (Dsys_sub_Tcolim s 0).master_eq, Dsys_master]

/-- The easy half of `T(𝒟) = 𝒟`: every neighbourhood of `𝒟` is a neighbourhood of
`T(𝒟)`
(`𝒟 ⊆ T(𝒟)`), since `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ}) ◁ T(𝒟)`. -/
theorem colim_sub_Tcolim (s : Setup.{w}) {X : Set s.Tok} (hX : (colim s).mem X) :
    (Tcolim s).mem X := by
  obtain ⟨n, hn⟩ := hX
  exact (Dsys_sub_Tcolim s n).sub ((Dchain s n).sub hn)

/-- **The continuity step (the hard half of `T(𝒟) = 𝒟`).** Every neighbourhood of
`T(𝒟)` is a
neighbourhood of `𝒟`. This is exactly Scott's `T(𝒟) = T(⋃ₙ Tⁿ({Γ})) = ⋃ₙ Tⁿ⁺¹({Γ})
= 𝒟`,
obtained from *continuity on domains* applied to the directed family `{Tⁿ({Γ})}`. -/
theorem Tcolim_sub_colim (s : Setup.{w}) {X : Set s.Tok} (hX : (Tcolim s).mem X) :
    (colim s).mem X := by
  obtain ⟨hmono', hC⟩ := s.hcont
  set ℱ : Set (NeighborhoodSystem s.Tok) := Set.range (Dsys s) with hℱdef
  have hℱ : ∀ ⦃D⦄, D ∈ ℱ → D ◁ colim s := by rintro D ⟨n, rfl⟩; exact Dsys_sub_colim s n
  have hne : ℱ.Nonempty := ⟨Dsys s 0, ⟨0, rfl⟩⟩
  have hdir : DirectedOn (· ◁ ·) ℱ := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    exact ⟨Dsys s (max n m), ⟨max n m, rfl⟩,
      chain_le s (le_max_left n m), chain_le s (le_max_right n m)⟩
  have hU : ∀ Y, (colim s).mem Y ↔ ∃ D ∈ ℱ, D.mem Y := by
    intro Y; constructor
    · rintro ⟨n, hn⟩; exact ⟨Dsys s n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨D, ⟨n, rfl⟩, hn⟩; exact ⟨n, hn⟩
  have heq := hC ℱ hℱ hne hdir (Subsystem.refl (colim s)) hU
  set Y₀ : Set (s.T.obj ⟨s.Tok, colim s⟩).carrier := (colimCeq s).symm ▸ X with hY₀
  -- `X ∈ T(𝒟)` says `Y₀ ∈ targetFam (refl 𝒟)` = the neighbourhood family of
  -- `T(𝒟)`.
  have hmem : Y₀ ∈ targetFam s.T hmono' (Subsystem.refl (colim s)) :=
    (mem_cast (colimCeq s) _ X).mp hX
  rw [heq, Set.mem_iUnion] at hmem
  obtain ⟨D, hmem⟩ := hmem
  rw [Set.mem_iUnion] at hmem
  obtain ⟨hD, hmemD⟩ := hmem
  obtain ⟨n, rfl⟩ := hD
  simp only [targetFam, Set.mem_setOf_eq] at hmemD
  -- conclude `X ∈ Tⁿ⁺¹({Γ}) ⊆ 𝒟`.
  refine ⟨n + 1, ?_⟩
  rw [Dsys_succ s n, mem_cast (Dceq s n)]
  have key : ((Dceq s n).symm ▸ X : Set (s.T.obj ⟨s.Tok, Dsys s n⟩).carrier)
      = (s.hmono (hℱ ⟨n, rfl⟩)).carrier_eq ▸ Y₀ := by
    rw [hY₀, set_rec_trans]
  rw [key]
  exact hmemD

/-- **`T(𝒟) = 𝒟`** (Scott's `𝒟 = T(𝒟)`): the two systems have the same
neighbourhoods (mutual
inclusion via `colim_sub_Tcolim`/`Tcolim_sub_colim`) and the same master. -/
theorem Tcolim_eq_colim (s : Setup.{w}) : Tcolim s = colim s :=
  NeighborhoodSystem.ext
    (fun _ => ⟨fun h => Tcolim_sub_colim s h, fun h => colim_sub_Tcolim s h⟩)
    (by rw [Tcolim_master, colim_master])

/-! ### `𝒟` is a `T`-algebra: the iso `𝒟 ≅ T(𝒟)` is the identity -/

/-- A `DomainObj` equality from a carrier equality and a transported-system
equality. -/
theorem domainObj_ext {c : Type w} (σ : NeighborhoodSystem c) (e : c = α)
    {V : NeighborhoodSystem α} (h : (e ▸ σ : NeighborhoodSystem α) = V) :
    (⟨c, σ⟩ : DomainObj) = ⟨α, V⟩ := by
  cases e; cases h; rfl

/-- The identity isomorphism induced by an object equality in any category. -/
def isoOfEq {Obj : Type*} [Category Obj] {X Y : Obj} (h : X = Y) : Iso X Y := by
  cases h
  exact ⟨Category.id X, Category.id X, Category.id_comp _, Category.id_comp _⟩

/-- **`T(𝒟) ≅ 𝒟` is the identity**, packaged as a `DomainObj` equality `T(𝒟) = 𝒟`. -/
theorem colimObj_eq (s : Setup.{w}) :
    s.T.obj ⟨s.Tok, colim s⟩ = (⟨s.Tok, colim s⟩ : DomainObj) :=
  domainObj_ext (s.T.obj ⟨s.Tok, colim s⟩).sys (colimCeq s) (Tcolim_eq_colim s)

/-- The isomorphism `T(𝒟) ≅ 𝒟` making `𝒟` a `T`-algebra (the identity, since `T(𝒟)
= 𝒟`). -/
def colimIso (s : Setup.{w}) : Iso (s.T.obj ⟨s.Tok, colim s⟩) (⟨s.Tok, colim s⟩ : DomainObj) :=
  isoOfEq (colimObj_eq s)

/-- The colimit `𝒟` as a `T`-algebra, with structure map the iso `T(𝒟) → 𝒟`. -/
def colimAlg (s : Setup.{w}) : TAlgebra s.T :=
  ⟨⟨s.Tok, colim s⟩, (colimIso s).hom⟩

/-! ### Existence of homomorphisms (Theorem 6.9) -/

/-- **Existence (Theorem 6.9 applied to `𝒟 ≅ T(𝒟)`).** For any `T`-algebra `B`
with a strict
structure map, there is a *strict* homomorphism `𝒟 → B`. -/
theorem nonempty_strict_algHom (s : Setup.{w}) (B : TAlgebra s.T) (hk : IsStrict B.str) :
    Nonempty {g : AlgHom (colimAlg s) B // IsStrict g.hom} :=
  nonempty_algHom_of_continuousOnMaps s.T s.hmaps (colimIso s) B hk

/-- **Existence (Theorem 6.9 applied to `𝒟 ≅ T(𝒟)`).** For any `T`-algebra `B`
with a strict
structure map, there is a homomorphism `𝒟 → B`. -/
theorem nonempty_algHom (s : Setup.{w}) (B : TAlgebra s.T) (hk : IsStrict B.str) :
    Nonempty (AlgHom (colimAlg s) B) :=
  (nonempty_strict_algHom s B hk).map (·.1)

/-! ### The projection chain `ρₙ = iₙ ∘ jₙ` and `⋃ₙ ρₙ = I_𝒟` -/

/-- `ρₙ = iₙ ∘ jₙ : 𝒟 → 𝒟`, the retraction onto `Tⁿ({Γ})` (Proposition 6.12's
projection pair for
`Tⁿ({Γ}) ◁ 𝒟`). -/
def rho (s : Setup.{w}) (n : ℕ) : ApproximableMap (colim s) (colim s) :=
  (Dsys_sub_colim s n).inj.comp (Dsys_sub_colim s n).proj

/-- Scott's relational description `X ρₙ Y ↔ ∃ z ∈ Tⁿ({Γ}), X ⊆ z ⊆ Y`. -/
theorem rho_rel (s : Setup.{w}) (n : ℕ) {X Y : Set s.Tok} :
    (rho s n).rel X Y ↔
      (colim s).mem X ∧ (colim s).mem Y ∧ ∃ z, (Dsys s n).mem z ∧ X ⊆ z ∧ z ⊆ Y := by
  unfold rho
  rw [comp_rel]
  constructor
  · rintro ⟨z, ⟨hcX, hDz, hXz⟩, _, hcY, hzY⟩
    exact ⟨hcX, hcY, z, hDz, hXz, hzY⟩
  · rintro ⟨hcX, hcY, z, hDz, hXz, hzY⟩
    exact ⟨z, ⟨hcX, hDz, hXz⟩, hDz, hcY, hzY⟩

/-- `ρₙ ⊆ ρₘ` for `n ≤ m` (the projection chain is increasing). -/
theorem rho_mono (s : Setup.{w}) {n m : ℕ} (h : n ≤ m) {X Y : Set s.Tok}
    (hr : (rho s n).rel X Y) : (rho s m).rel X Y := by
  rw [rho_rel] at hr ⊢
  obtain ⟨hcX, hcY, z, hDz, hXz, hzY⟩ := hr
  exact ⟨hcX, hcY, z, (chain_le s h).sub hDz, hXz, hzY⟩

/-- The pointwise union `⋃ₙ ρₙ` (directed, since the chain is increasing). -/
def iSupRho (s : Setup.{w}) : ApproximableMap (colim s) (colim s) :=
  iSupMap (rho s) (fun i j => ⟨max i j,
    fun _ _ h => rho_mono s (le_max_left i j) h,
    fun _ _ h => rho_mono s (le_max_right i j) h⟩)

/-- **`⋃ₙ ρₙ = I_𝒟`** (Scott's key identity for uniqueness). The forward inclusion
uses
`X ⊆ z ⊆ Y ⟹ X ⊆ Y`; the reverse factors the identity step `X ⊆ X ⊆ Y` through the
level
witnessing `X ∈ 𝒟`. -/
theorem iSupRho_eq_id (s : Setup.{w}) : iSupRho s = idMap (colim s) := by
  apply ApproximableMap.ext
  intro X Y
  rw [idMap_rel]
  constructor
  · rintro ⟨n, hr⟩
    rw [rho_rel] at hr
    obtain ⟨hcX, hcY, z, _, hXz, hzY⟩ := hr
    exact ⟨hcX, hcY, hXz.trans hzY⟩
  · rintro ⟨hcX, hcY, hXY⟩
    obtain ⟨n, hX⟩ := hcX
    exact ⟨n, (rho_rel s n).mpr ⟨⟨n, hX⟩, hcY, X, hX, subset_rfl, hXY⟩⟩

/-! ### Theorem 6.14 — the existence half (the canonical solution and its
homomorphisms) -/

/-- **Theorem 6.14 (Scott 1981, PRG-19) — the canonical fixed point.** Under the
hypotheses
(continuous on maps, monotone and continuous on domains, with a generating set
`{Γ} ◁ T({Γ})`), the
iterated colimit `𝒟 = ⋃ₙ Tⁿ({Γ})` is a `T`-algebra whose structure map is an
isomorphism
`T(𝒟) ≅ 𝒟` (the identity, since `T(𝒟) = 𝒟`), and there is a homomorphism from `𝒟`
into every
`T`-algebra with a strict structure map (Theorem 6.9). This is Scott's *existence*
of the initial
`T`-algebra. -/
theorem exists_algebra_with_hom (s : Setup.{w}) :
    ∃ A : TAlgebra s.T, Nonempty (Iso (s.T.obj A.carrier) A.carrier) ∧
      ∀ B : TAlgebra s.T, IsStrict B.str → Nonempty (AlgHom A B) :=
  ⟨colimAlg s, ⟨colimIso s⟩, fun B hk => nonempty_algHom s B hk⟩

/-! ### Theorem 6.14 — the uniqueness half (`T(ρₙ) = ρₙ₊₁`, then `g = ⋃ₙ g∘ρₙ`)

Scott shows homomorphisms out of `𝒟` are unique by showing they are determined on
the finite
elements. Concretely, the projection chain `ρₙ = iₙ ∘ jₙ` satisfies `T(ρₙ) = ρₙ₊₁`
(because `T` is
monotone on domains, so it carries the projection pair `iₙ, jₙ` to `iₙ₊₁, jₙ₊₁`)
and
`⋃ₙ ρₙ = I_𝒟`. For any homomorphism `g : 𝒟 → E`, the sequence `gₙ = g ∘ ρₙ` is
then **independent
of `g`**: `g₀ = ⊥` (because `g` is strict and `ρ₀ = ⊥`), and `gₙ₊₁ = k ∘ T(gₙ) ∘
j` by the
homomorphism square; so `g = ⋃ₙ gₙ` is forced. -/

/-- In the category of domains, `⊚` (categorical composition) is
`ApproximableMap.comp`. -/
theorem cat_comp_eq {X Y Z : DomainObj} (g : Category.Hom Y Z) (f : Category.Hom X Y) :
    g ⊚ f = g.comp f := rfl

/-- The colimit `𝒟` as a category object `⟨Tok, 𝒟⟩`. -/
abbrev objColim (s : Setup.{w}) : DomainObj := ⟨s.Tok, colim s⟩

/-- The `n`-th tower system `Tⁿ({Γ})` as a category object `⟨Tok, Tⁿ({Γ})⟩`. -/
abbrev objDsys (s : Setup.{w}) (n : ℕ) : DomainObj := ⟨s.Tok, Dsys s n⟩

/-- `T(ρₙ)` as an endomorphism of `T(𝒟)`, with the category objects pinned (they
cannot be inferred
from `rho s n`'s `ApproximableMap` type alone). -/
abbrev tmapRho (s : Setup.{w}) (n : ℕ) :
    ApproximableMap (s.T.obj (objColim s)).sys (s.T.obj (objColim s)).sys :=
  s.T.map (X := objColim s) (Y := objColim s) (rho s n)

/-- Transport of a `Hom X X` along an object equality is heterogeneously equal to
itself. -/
theorem transport_heq {Obj : Type*} [Category Obj] {X Y : Obj} (e : X = Y)
    (f : Category.Hom X X) : HEq (e ▸ f : Category.Hom Y Y) f := by
  cases e; rfl

/-- Conjugation by the identity isomorphism `isoOfEq e` is the object-transport
along `e`. -/
theorem isoOfEq_conj {Obj : Type*} [Category Obj] {X Y : Obj} (e : X = Y)
    (f : Category.Hom X X) :
    (isoOfEq e).hom ⊚ f ⊚ (isoOfEq e).inv = (e ▸ f : Category.Hom Y Y) := by
  cases e
  change Category.id X ⊚ f ⊚ Category.id X = f
  rw [Category.id_comp, Category.comp_id]

/-- **The carrier-transport core of `T(ρₙ) = ρₙ₊₁`.** Given the
*monotone-on-domains* data for a
subsystem (its injection `Tmi`/projection `Tmj` are heterogeneously equal to the
canonical 6.12 pair
`sub.inj`/`sub.proj` of the image subsystem `sub : Ps ◁ ce ▸ Qs`), the composite
`Tmi ∘ Tmj` is —
after carrying the functor-image carriers `Pc, Qc` down to `Tok` — exactly the
projection
`iₙ₊₁ ∘ jₙ₊₁` of the next subsystem `hsub' : Dn1 ◁ Col`. Proved by `subst`ing the
carrier equalities,
after which proof-irrelevance identifies the two subsystem proofs. -/
theorem map_comp_proj_heq {Tok : Type w} {Pc Qc : Type w} (cn : Pc = Tok) (cc : Qc = Tok)
    {Ps : NeighborhoodSystem Pc} {Qs : NeighborhoodSystem Qc} (ce : Qc = Pc)
    (sub : Ps ◁ (ce ▸ Qs : NeighborhoodSystem Pc))
    {Dn1 Col : NeighborhoodSystem Tok}
    (hDn1 : (cn ▸ Ps : NeighborhoodSystem Tok) = Dn1)
    (hCol : (cc ▸ Qs : NeighborhoodSystem Tok) = Col)
    (hsub' : Dn1 ◁ Col)
    (Tmi : ApproximableMap Ps Qs) (Tmj : ApproximableMap Qs Ps)
    (hi : HEq Tmi sub.inj) (hj : HEq Tmj sub.proj) :
    HEq (Tmi.comp Tmj) (hsub'.inj.comp hsub'.proj) := by
  subst cn
  subst cc
  obtain rfl := hDn1
  obtain rfl := hCol
  have e1 : Tmi = sub.inj := eq_of_heq hi
  have e2 : Tmj = sub.proj := eq_of_heq hj
  rw [e1, e2]

/-- **`T(ρₙ) = ρₙ₊₁`, heterogeneously.** The image `T(ρₙ)` of the `n`-th
projection, living over
`T(𝒟)`'s carrier, is heterogeneously equal to the `(n+1)`-st projection `ρₙ₊₁`
over `Tok`. -/
theorem map_rho_heq (s : Setup.{w}) (n : ℕ) :
    HEq (tmapRho s n) (rho s (n + 1)) := by
  have hcomp : tmapRho s n
      = (s.T.map (X := objDsys s n) (Y := objColim s) (Dsys_sub_colim s n).inj).comp
          (s.T.map (X := objColim s) (Y := objDsys s n) (Dsys_sub_colim s n).proj) :=
    s.T.map_comp (X := objColim s) (Y := objDsys s n) (Z := objColim s)
      (Dsys_sub_colim s n).inj (Dsys_sub_colim s n).proj
  rw [hcomp]
  exact map_comp_proj_heq (Dceq s n) (colimCeq s) (s.hmono (Dsys_sub_colim s n)).carrier_eq
    (s.hmono (Dsys_sub_colim s n)).sub (Dsys_succ s n).symm (Tcolim_eq_colim s)
    (Dsys_sub_colim s (n +
      1)) (s.T.map (X := objDsys s n) (Y := objColim s) (Dsys_sub_colim s n).inj)
    (s.T.map (X := objColim s) (Y := objDsys s n) (Dsys_sub_colim s n).proj)
    (s.hmono (Dsys_sub_colim s n)).inj_heq (s.hmono (Dsys_sub_colim s n)).proj_heq

/-- **`ρₙ₊₁ = i ∘ T(ρₙ) ∘ j`** (Scott's `T(ρₙ) = ρₙ₊₁`, conjugated by the
structure iso). Since the
iso `𝒟 ≅ T(𝒟)` is the identity, this is the carrier transport of `T(ρₙ)`; combined
with
`map_rho_heq` it pins `ρₙ₊₁`. -/
theorem key_rho (s : Setup.{w}) (n : ℕ) :
    rho s (n + 1) = (colimIso s).hom ⊚ tmapRho s n ⊚ (colimIso s).inv := by
  rw [show (colimIso s).hom = (isoOfEq (colimObj_eq s)).hom from rfl,
      show (colimIso s).inv = (isoOfEq (colimObj_eq s)).inv from rfl,
      isoOfEq_conj (colimObj_eq s) (tmapRho s n)]
  apply eq_of_heq
  exact HEq.trans (map_rho_heq s n).symm
    (transport_heq (colimObj_eq s) (tmapRho s n)).symm

/-! ### The `g`-independent fixed-point recursion -/

/-- For a strict map `g`, `g(⊥) = ⊥` relationally: `g` sends `Δ` only to `Δ`. -/
theorem strict_rel_master {β₀ β₁ : Type w} {V₀ : NeighborhoodSystem β₀}
    {V₁ : NeighborhoodSystem β₁} {g : ApproximableMap V₀ V₁} (hg : IsStrict g) {Z : Set β₁} :
    g.rel V₀.master Z ↔ Z = V₁.master :=
  ⟨fun h => hg h, fun h => h ▸ g.master_rel⟩

/-- `Dsys s 0 = Γ` (the base of the tower). -/
@[simp] theorem Dsys_zero (s : Setup.{w}) : Dsys s 0 = s.Γ := rfl

/-- **`ρ₀ = ⊥`** when `{Γ}` is the trivial one-point system: `ρ₀` relates `X` only
to the master.
This is where Scott's `{Γ}` (a *one-point* domain) is used. -/
theorem rho_zero_rel (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    {X Y : Set s.Tok} :
    (rho s 0).rel X Y ↔ (colim s).mem X ∧ Y = (colim s).master := by
  rw [rho_rel]
  constructor
  · rintro ⟨hcX, hcY, z, hz, _, hzY⟩
    have hzm : z = s.Γ.master := hΓ z hz
    subst hzm
    refine ⟨hcX, Set.Subset.antisymm ((colim s).sub_master hcY) ?_⟩
    rw [colim_master]; exact hzY
  · rintro ⟨hcX, rfl⟩
    refine ⟨hcX, (colim s).master_mem, s.Γ.master, s.Γ.master_mem, ?_, ?_⟩
    · have h := (colim s).sub_master hcX; rwa [colim_master] at h
    · rw [colim_master]

/-- For a strict homomorphism `g`, the base `g ∘ ρ₀` is the least map: it relates
`X` only to the
master of `E`, independent of `g`. -/
theorem gcomp_rho_zero_rel (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) {g : ApproximableMap (colim s) B.carrier.sys} (hg : IsStrict g)
    {X : Set s.Tok} {Z : Set B.carrier.carrier} :
    (g.comp (rho s 0)).rel X Z ↔ (colim s).mem X ∧ Z = B.carrier.sys.master := by
  rw [comp_rel]
  constructor
  · rintro ⟨Y, hrho, hgYZ⟩
    rw [rho_zero_rel s hΓ] at hrho
    obtain ⟨hcX, rfl⟩ := hrho
    exact ⟨hcX, (strict_rel_master hg).mp hgYZ⟩
  · rintro ⟨hcX, rfl⟩
    exact ⟨(colim s).master, (rho_zero_rel s hΓ).mpr ⟨hcX, rfl⟩, g.master_rel⟩

/-- The base case of `g`-independence: any two strict maps agree after `∘ ρ₀`. -/
theorem gcomp_rho_zero_indep (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) {g g' : ApproximableMap (colim s) B.carrier.sys}
    (hg : IsStrict g) (hg' : IsStrict g') :
    g.comp (rho s 0) = g'.comp (rho s 0) := by
  apply ApproximableMap.ext
  intro X Z
  rw [gcomp_rho_zero_rel s hΓ B hg, gcomp_rho_zero_rel s hΓ B hg']

/-- **The fixed-point recursion `gₙ₊₁ = k ∘ T(gₙ) ∘ j`.** Using `key_rho` (`ρₙ₊₁ =
i∘T(ρₙ)∘j`)
and the
homomorphism square `g ∘ i = k ∘ T(g)`. -/
theorem gcomp_rho_succ (s : Setup.{w}) (B : TAlgebra s.T) (g : AlgHom (colimAlg s) B) (n : ℕ) :
    g.hom.comp (rho s (n + 1))
      = B.str.comp ((s.T.map (X := objColim s) (Y := B.carrier)
          (g.hom.comp (rho s n))).comp (colimIso s).inv) := by
  have hcomm : g.hom ⊚ (colimIso s).hom
      = B.str ⊚ s.T.map (X := objColim s) (Y := B.carrier) g.hom := g.comm
  change g.hom ⊚ rho s (n + 1)
      = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) (g.hom ⊚ rho s n)) ⊚ (colimIso s).inv
  calc g.hom ⊚ rho s (n + 1)
      = g.hom ⊚ ((colimIso s).hom ⊚ (tmapRho s n ⊚ (colimIso s).inv)) :=
          congrArg (fun x => g.hom ⊚ x) (key_rho s n)
    _ = (g.hom ⊚ (colimIso s).hom) ⊚ (tmapRho s n ⊚ (colimIso s).inv) :=
          (Category.assoc g.hom (colimIso s).hom (tmapRho s n ⊚ (colimIso s).inv)).symm
    _ = (B.str ⊚ s.T.map (X := objColim s) (Y := B.carrier) g.hom)
            ⊚ (tmapRho s n ⊚ (colimIso s).inv) := by rw [hcomm]
    _ = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) g.hom
            ⊚ (tmapRho s n ⊚ (colimIso s).inv)) :=
          Category.assoc B.str (s.T.map (X := objColim s) (Y := B.carrier) g.hom)
            (tmapRho s n ⊚ (colimIso s).inv)
    _ = B.str ⊚ ((s.T.map (X := objColim s) (Y := B.carrier) g.hom ⊚ tmapRho s n)
            ⊚ (colimIso s).inv) :=
          congrArg (B.str ⊚ ·)
            (Category.assoc (s.T.map (X := objColim s) (Y := B.carrier) g.hom) (tmapRho s n)
              (colimIso s).inv).symm
    _ = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) (g.hom ⊚ rho s n)
            ⊚ (colimIso s).inv) :=
          congrArg (fun m => B.str ⊚ (m ⊚ (colimIso s).inv))
            (s.T.map_comp (X := objColim s) (Y := objColim s) (Z := B.carrier) g.hom
              (rho s n)).symm

/-- **`g`-independence of `gₙ = g ∘ ρₙ`.** For any two strict homomorphisms into
the same algebra,
`g ∘ ρₙ = g' ∘ ρₙ` for all `n` — the sequence is determined by the recursion, not
by `g`. -/
theorem gcomp_rho_indep (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (g g' : AlgHom (colimAlg s) B)
    (hg : IsStrict g.hom) (hg' : IsStrict g'.hom) (n : ℕ) :
    g.hom.comp (rho s n) = g'.hom.comp (rho s n) := by
  induction n with
  | zero => exact gcomp_rho_zero_indep s hΓ B hg hg'
  | succ k ih => rw [gcomp_rho_succ s B g k, gcomp_rho_succ s B g' k, ih]

/-! ### Uniqueness and initiality (among strict algebras) -/

/-- Two algebra homomorphisms with equal underlying maps are equal (the commuting
square is a
`Prop`). -/
theorem algHom_ext {Obj : Type*} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}
    {g g' : AlgHom A B} (h : g.hom = g'.hom) : g = g' := by
  cases g; cases g'; cases h; rfl

/-- **The underlying maps of two strict homomorphisms coincide**: `g = g ∘ I = g ∘
⋃ₙ ρₙ =
⋃ₙ (g ∘ ρₙ)`, and the latter is `g`-independent. -/
theorem gcomp_eq (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (g g' : AlgHom (colimAlg s) B)
    (hg : IsStrict g.hom) (hg' : IsStrict g'.hom) :
    g.hom = g'.hom := by
  have key : g.hom.comp (iSupRho s) = g'.hom.comp (iSupRho s) := by
    apply ApproximableMap.ext
    intro X Z
    rw [comp_rel, comp_rel]
    constructor
    · rintro ⟨Y, ⟨n, hrho⟩, hgYZ⟩
      have hin : (g.hom.comp (rho s n)).rel X Z := ⟨Y, hrho, hgYZ⟩
      rw [gcomp_rho_indep s hΓ B g g' hg hg' n] at hin
      obtain ⟨Y', hrho', hgYZ'⟩ := hin
      exact ⟨Y', ⟨n, hrho'⟩, hgYZ'⟩
    · rintro ⟨Y, ⟨n, hrho⟩, hgYZ⟩
      have hin : (g'.hom.comp (rho s n)).rel X Z := ⟨Y, hrho, hgYZ⟩
      rw [← gcomp_rho_indep s hΓ B g g' hg hg' n] at hin
      obtain ⟨Y', hrho', hgYZ'⟩ := hin
      exact ⟨Y', ⟨n, hrho'⟩, hgYZ'⟩
  have e : g.hom.comp (idMap (colim s)) = g.hom := comp_idMap g.hom
  have e' : g'.hom.comp (idMap (colim s)) = g'.hom := comp_idMap g'.hom
  rw [← e, ← e', ← iSupRho_eq_id]
  exact key

/-- **Uniqueness of strict homomorphisms out of `𝒟`.** Any two strict `T`-algebra
homomorphisms from
the canonical solution into the same algebra are equal. -/
theorem algHom_unique (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (g g' : AlgHom (colimAlg s) B)
    (hg : IsStrict g.hom) (hg' : IsStrict g'.hom) : g = g' :=
  algHom_ext (gcomp_eq s hΓ B g g' hg hg')

/-- **Theorem 6.14 (Scott 1981, PRG-19) — initial `T`-algebra.** When `{Γ}` is the
one-point
generating system, the canonical solution `𝒟 = ⋃ₙ Tⁿ({Γ})` is the **initial**
`T`-algebra among the
strict algebras: for every `T`-algebra `B` with a strict structure map there is a
*unique* strict
homomorphism `𝒟 → B`. (Existence is Theorem 6.9; uniqueness is the `ρₙ`
projection-chain argument.) -/
theorem exists_unique_strict_algHom (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (hk : IsStrict B.str) :
    ∃ g : AlgHom (colimAlg s) B, IsStrict g.hom ∧
      ∀ g' : AlgHom (colimAlg s) B, IsStrict g'.hom → g' = g := by
  obtain ⟨⟨g, hg⟩⟩ := nonempty_strict_algHom s B hk
  exact ⟨g, hg, fun g' hg' => algHom_unique s hΓ B g' g hg' hg⟩

end Theorem614

end Domain.Neighborhood
