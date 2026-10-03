/-
Copyright (c) 2026 Aditya Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Rao
-/

module
public import LeanPool.KrohnRhodes.Foundations.GreenRelations
public import LeanPool.KrohnRhodes.Foundations.LocalDivisor
public import LeanPool.KrohnRhodes.Foundations.KrasnerKaloujnine
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Push

/-!
# Krohn–Rhodes factor towers

This file supplies the vocabulary for the aperiodic/simple-group decomposition variant, and
the wreath-product algebra used to assemble factor towers.

* `KRFactor` — a finite monoid together with a *witnessed* flag: either every element is
  aperiodic, or the carrier carries a simple group structure whose underlying monoid is the
  factor's monoid. Constructors `KRFactor.ofAperiodic` and `KRFactor.ofSimpleGroup`.
* `DivTowerWreath M [F₁, …, Fₖ]` — a recursive sequence of wreath divisions.
  It is defined by recursion on the list: `M` divides
  `WreathProduct F₁ B Y` for some finite monoid `B` acting on a finite type `Y`, where `B`
  in turn satisfies `DivTowerWreath B [F₂, …, Fₖ]`; the empty list means `M` is trivial.
* Wreath-product algebra: associativity up to division (`sgDiv_wreath_assoc`, via the
  embedding `WreathAssoc.Phi`), monotonicity in the decoration (`sgDiv_wreath_decoration_mono`),
  the concatenation step `divTowerWreath_wreathStep`, and `divTowerWreath_of_sgDiv` (towers
  pull back along division).
* `group_subquotient_faithful_aux` — every finite group has a factor tower all of whose
  factors divide the group; the construction uses only simple groups (induction along a
  normal subgroup, using the Krasner–Kaloujnine embedding of `KrasnerKaloujnine.lean`).

## References

* [K. Krohn, J. Rhodes, *Algebraic Theory of Machines. I. Prime Decomposition Theorem for
  Finite Semigroups and Machines*, Trans. AMS 116 (1965), 450–464]
* [Eilenberg, *Automata, Languages, and Machines, Vol. B*, 1976]
-/

public section

namespace LeanPool.KrohnRhodes

universe u

open Green

/-- **Division is reflexive** for semigroups. `S` divides itself via the
    identity homomorphism on the whole semigroup. -/
theorem sgDiv_refl (S : Type u) [Semigroup S] : SgDiv S S := by
  refine ⟨⊤, ⟨fun ⟨x, _⟩ => x, ?_⟩, ?_⟩
  · intro ⟨_, _⟩ ⟨_, _⟩; rfl
  · intro s; exact ⟨⟨s, Subsemigroup.mem_top s⟩, rfl⟩

/-!
## Factor towers

A *factor tower* of a finite monoid `M` is an explicit list of Krohn–Rhodes factors
`[F₁, …, Fₖ]`, each flagged and witnessed as aperiodic or simple group, together with a proof
of the recursive division predicate `DivTowerWreath M [F₁, …, Fₖ]`.
The intermediate base monoids and their actions are existential witnesses at each step;
this file does not identify the tower with a single prescribed transformation wreath product.

* `KRFactorKind`, `KRFactor` — the two factor kinds, and one flagged, witnessed factor.
* `DivTowerWreath M factors` — the recursive division predicate.
* `divTowerWreath_wreathStep` — concatenation of towers along a wreath division; the hard step
  (wreath associativity) is `sgDiv_wreath_assoc`.
-/

/-- The two kinds of factors used here: a finite aperiodic monoid or a finite simple group.
The aperiodic factors need not be irreducible or three-element reset monoids. -/
inductive KRFactorKind where
  /-- The factor is a finite aperiodic monoid. -/
  | aperiodic : KRFactorKind
  /-- The factor is a finite simple group. -/
  | simpleGroup : KRFactorKind
  deriving DecidableEq, Repr

/-- A single **Krohn-Rhodes factor**: a finite monoid `carrier` together with a
    flag `kind` and a *proof* that `carrier` really satisfies its flag.  The
    proof field is what makes the decomposition genuinely informative (not a
    vacuous existential): an `aperiodic` factor must actually be aperiodic
    (every element has a trivial `H`-class), and a `simpleGroup` factor must
    actually carry a `Group` instance that is `IsSimpleGroup`. -/
structure KRFactor where
  /-- The carrier monoid of the factor. -/
  carrier : Type u
  /-- The factor's monoid structure. -/
  [mon : Monoid carrier]
  /-- The factor is finite. -/
  [fin : Finite carrier]
  /-- Whether the factor is an aperiodic factor or a simple-group factor. -/
  kind : KRFactorKind
  /-- The flag is *witnessed*: an `aperiodic`-flagged factor is genuinely
      aperiodic; a `simpleGroup`-flagged factor genuinely carries a finite
      simple-group structure on `carrier` **whose underlying monoid is the
      factor's own monoid field** (`g.toMonoid = mon`).  Recording the
      `g.toMonoid = mon` compatibility lets one transport monoid-indexed data
      between `F.mon` and the witnessed group instance `g`. -/
  isKind :
    (kind = KRFactorKind.aperiodic ∧ (∀ a : carrier, IsAperiodicElem a)) ∨
    (kind = KRFactorKind.simpleGroup ∧
      ∃ (g : Group carrier), g.toMonoid = mon ∧ @IsSimpleGroup carrier g)

attribute [instance] KRFactor.mon KRFactor.fin

namespace KRFactor

/-- Build an aperiodic factor from a finite aperiodic monoid. -/
@[expose]
def ofAperiodic (A : Type u) [Monoid A] [Finite A]
    (hA : ∀ a : A, IsAperiodicElem a) : KRFactor.{u} where
  carrier := A
  kind := KRFactorKind.aperiodic
  isKind := Or.inl ⟨rfl, hA⟩

/-- Build a simple-group factor from a finite simple group. -/
@[expose]
def ofSimpleGroup (G : Type u) [g : Group G] [Finite G] [IsSimpleGroup G] :
    KRFactor.{u} where
  carrier := G
  kind := KRFactorKind.simpleGroup
  isKind := Or.inr ⟨rfl, ⟨g, rfl, inferInstance⟩⟩

@[simp] theorem ofAperiodic_carrier (A : Type u) [Monoid A] [Finite A]
    (hA : ∀ a : A, IsAperiodicElem a) : (ofAperiodic A hA).carrier = A := rfl

@[simp] theorem ofAperiodic_kind (A : Type u) [Monoid A] [Finite A]
    (hA : ∀ a : A, IsAperiodicElem a) :
    (ofAperiodic A hA).kind = KRFactorKind.aperiodic := rfl

@[simp] theorem ofSimpleGroup_carrier (G : Type u) [Group G] [Finite G]
    [IsSimpleGroup G] : (ofSimpleGroup G).carrier = G := rfl

@[simp] theorem ofSimpleGroup_kind (G : Type u) [Group G] [Finite G]
    [IsSimpleGroup G] : (ofSimpleGroup G).kind = KRFactorKind.simpleGroup := rfl

end KRFactor

/-- **The recursive division predicate of a factor tower.**

    `DivTowerWreath M factors` records the following recursive wreath divisions:

    * `[]`           — `M` divides the trivial monoid `PUnit` (the empty product;
                       this forces `M` to be a single point up to division).
    * `F :: rest`    — there is a finite base monoid `B` that itself decomposes
                       via the *tail* `rest` (`DivTowerWreath B rest`), and `M`
                       divides `WreathProduct F.carrier B Y` for some finite type
                       `Y` on which `B` acts: the head factor `F.carrier` sits in
                       the decoration slot over the base `B`.

    No action-lifting or equivalence with a single iterated transformation wreath product
    is asserted by this definition. The intermediate base at each step has its own tower. -/
@[expose]
def DivTowerWreath : (M : Type u) → [Monoid M] → [Finite M] → List KRFactor.{u} → Prop
  | M, _, _, [] => SgDiv M PUnit.{u + 1}
  | M, _, _, (F :: rest) =>
      ∃ (B : Type u) (_ : Monoid B) (_ : Finite B)
        (Y : Type u) (_ : Fintype Y) (_ : MulAction B Y),
        DivTowerWreath B rest ∧
        SgDiv M (WreathProduct F.carrier B Y)

@[simp] theorem divTowerWreath_nil (M : Type u) [Monoid M] [Finite M] :
    DivTowerWreath M [] = SgDiv M PUnit.{u + 1} := rfl

theorem divTowerWreath_cons (M : Type u) [Monoid M] [Finite M]
    (F : KRFactor.{u}) (rest : List KRFactor.{u}) :
    DivTowerWreath M (F :: rest) ↔
      ∃ (B : Type u) (_ : Monoid B) (_ : Finite B)
        (Y : Type u) (_ : Fintype Y) (_ : MulAction B Y),
        DivTowerWreath B rest ∧
        SgDiv M (WreathProduct F.carrier B Y) := Iff.rfl

/-! ### Base-case constructors for the factor tower -/

/-- A single finite factor `A` over a *subsingleton* base `B` divides `A ≀_B B`
    (the wreath of `A` over the trivial base, with `B` acting on itself).  This
    is the "one rung" building block: when `B` is a single point the wreath
    multiplication collapses to a copy of `A`.

    Stated for a general subsingleton `B` (rather than literally `PUnit`) so that
    the wreath-product instances match exactly those produced by the cons case of
    `DivTowerWreath` at the call site (avoiding `MulAction PUnit PUnit` instance
    ambiguity). -/
theorem sgDiv_wreath_subsingleton_base (A B : Type u) [Monoid A] [Monoid B]
    [Subsingleton B] :
    SgDiv A (WreathProduct A B B) := by
  -- Embed `A` as `a ↦ ⟨fun _ => a, 1⟩`, with the top subsemigroup mapped back by
  -- evaluating the decoration at the (unique) point `1`.
  refine ⟨⊤, ⟨fun w => w.1.func 1, ?_⟩, ?_⟩
  · -- multiplicativity of the readout on the whole wreath:
    -- `(p * q).func 1 = p.func (q.base • 1) * q.func 1`, and `q.base • 1 = 1`
    -- since the base type is a subsingleton.
    rintro ⟨p, -⟩ ⟨q, -⟩
    change (p * q).func 1 = p.func 1 * q.func 1
    have hb : q.base • (1 : B) = (1 : B) := Subsingleton.elim _ _
    rw [WreathProduct.mul_func, hb]
  · -- surjectivity: hit `a` by `⟨fun _ => a, 1⟩`.
    intro a
    exact ⟨⟨⟨fun _ => a, 1⟩, Subsemigroup.mem_top _⟩, rfl⟩

/-- The empty factor tower for a subsingleton monoid: a subsingleton `M`
    divides `PUnit`. -/
theorem divTowerWreath_nil_of_subsingleton (M : Type u) [Monoid M] [Finite M]
    [Subsingleton M] : DivTowerWreath M ([] : List KRFactor.{u}) := by
  rw [divTowerWreath_nil]
  -- `SgDiv M PUnit`: the top subsemigroup of `PUnit` maps onto `M` (which is a
  -- single point) by `_ ↦ 1`.
  refine ⟨⊤, ⟨fun _ => (1 : M), fun _ _ => Subsingleton.elim _ _⟩, ?_⟩
  intro m
  exact ⟨⟨PUnit.unit, Subsemigroup.mem_top _⟩, Subsingleton.elim _ _⟩

/-- A single-factor tower over a factor `F`: `DivTowerWreath F.carrier [F]`,
    witnessed by the `PUnit` base.  (Stated directly over `F.carrier` with its
    canonical `F.mon`/`F.fin` instances so the wreath-product instances coincide
    with the recursive predicate's.) -/
theorem divTowerWreath_single (F : KRFactor.{u}) :
    DivTowerWreath F.carrier [F] := by
  rw [divTowerWreath_cons]
  refine ⟨PUnit.{u + 1}, inferInstance, inferInstance, PUnit.{u + 1},
    inferInstance, inferInstance, divTowerWreath_nil_of_subsingleton PUnit.{u + 1}, ?_⟩
  exact sgDiv_wreath_subsingleton_base F.carrier PUnit.{u + 1}

/-- **Single aperiodic factor tower.**  A finite aperiodic monoid `M` has the
    one-element factor tower `[KRFactor.ofAperiodic M hAper]`. -/
theorem divTowerWreath_ofAperiodic (M : Type u) [Monoid M] [Finite M]
    (hAper : ∀ a : M, IsAperiodicElem a) :
    DivTowerWreath M [KRFactor.ofAperiodic M hAper] :=
  divTowerWreath_single (KRFactor.ofAperiodic M hAper)

/-- **Single simple-group factor tower.**  A finite simple group `G` has the
    one-element factor tower `[KRFactor.ofSimpleGroup G]`. -/
theorem divTowerWreath_ofSimpleGroup (G : Type u) [Group G] [Finite G]
    [IsSimpleGroup G] :
    DivTowerWreath G [KRFactor.ofSimpleGroup G] :=
  divTowerWreath_single (KRFactor.ofSimpleGroup G)

/-! ### Division compatibility of the factor tower

The tower predicate is monotone under semigroup division on the left: if `S`
divides `T` and `T` has a recursive wreath-division tower, then so does
`S`.  It is used to transfer a tower along a division
`SgDiv S (WreathProduct A B X)`. -/

/-- **Division transfers the factor tower.**  If `SgDiv S T` and
    `DivTowerWreath T factors`, then `DivTowerWreath S factors`. -/
theorem divTowerWreath_of_sgDiv {S T : Type u} [Monoid S] [Finite S]
    [Monoid T] [Finite T] (h : SgDiv S T) :
    ∀ {factors : List KRFactor.{u}}, DivTowerWreath T factors →
      DivTowerWreath S factors := by
  intro factors
  cases factors with
  | nil =>
      intro hT
      rw [divTowerWreath_nil] at hT ⊢
      exact sgDiv_trans h hT
  | cons F rest =>
      intro hT
      rw [divTowerWreath_cons] at hT ⊢
      obtain ⟨B, mB, fB, Y, fY, aY, hBrest, hTw⟩ := hT
      exact ⟨B, mB, fB, Y, fY, aY, hBrest,
        sgDiv_trans h hTw⟩

/-! ### Wreath associativity (the inductive-step engine)

To combine towers of the decoration factor `A` and the base factor `B` (in
`S ≼ A ≀ B`) into a *single* factor list we need the classical **associativity
of the wreath product up to division**: a wreath nested in the decoration slot
re-associates into the base.

For the left-action convention
`(p * q).func x = p.func (q.base • x) * q.func x`, the precise associativity is

  `(G ≀_{B'} B') ≀_X B  ≼  G ≀_W (B' × X)`,   where `W = B' ≀_X B`,

with `W` acting on the product state space `B' × X` by the imprimitive action
`⟨γ, b⟩ • (p, x) = (γ x * p, b • x)`.  This is the standard wreath-associativity
theorem (Eilenberg, *Automata, Languages and Machines*, Vol. B, Ch. III; Wells,
"Some applications of the wreath product construction", 1976), realised by the
canonical "unscrambling" embedding `Phi` below.  The `q.base • x` cocycle threads
through both levels exactly because the inner state action of `B'` on `B'` is left
multiplication. -/

namespace WreathAssoc

variable (G B' B Y X : Type u) [Monoid G] [Monoid B'] [Monoid B]
  [MulAction B' Y] [MulAction B X]

/-- The imprimitive action of the base wreath `W = B' ≀_X B` on the product state
    space `Y × X`: `⟨γ, b⟩ • (y, x) = (γ x • y, b • x)` — the inner base `B'`
    acts on the inner state `Y`, the outer base `B` acts on the outer state `X`. -/
@[instance_reducible]
def actW : MulAction (WreathProduct B' B X) (Y × X) where
  smul w yx := (w.func yx.2 • yx.1, w.base • yx.2)
  one_smul := by
    rintro ⟨y, x⟩
    change ((1 : WreathProduct B' B X).func x • y, (1 : WreathProduct B' B X).base • x) = (y, x)
    rw [WreathProduct.one_func, WreathProduct.one_base, one_smul, one_smul]
  mul_smul := by
    rintro w1 w2 ⟨y, x⟩
    change ((w1 * w2).func x • y, (w1 * w2).base • x) =
         (w1.func (w2.base • x) • (w2.func x • y), w1.base • (w2.base • x))
    rw [WreathProduct.mul_func, WreathProduct.mul_base, mul_smul, mul_smul]

attribute [local instance] actW

/-- The canonical unscrambling embedding
    `(G ≀_{B'} Y) ≀_X B →ₙ* G ≀_W (Y × X)` realising wreath associativity:
    the two-level decoration `F` becomes the one-level decoration
    `(y, x) ↦ (F.func x).func y`, and the bases collect to
    `⟨fun x => (F.func x).base, F.base⟩`. -/
def Phi : WreathProduct (WreathProduct G B' Y) B X →ₙ*
    WreathProduct G (WreathProduct B' B X) (Y × X) where
  toFun F := ⟨fun yx => (F.func yx.2).func yx.1, ⟨fun x => (F.func x).base, F.base⟩⟩
  map_mul' := by
    intro F1 F2
    apply WreathProduct.ext
    · funext yx
      obtain ⟨y, x⟩ := yx
      change ((F1 * F2).func x).func y =
          (F1.func (F2.base • x)).func ((F2.func x).base • y) * (F2.func x).func y
      rw [WreathProduct.mul_func, WreathProduct.mul_func]
    · apply WreathProduct.ext
      · funext x; rfl
      · rfl

theorem Phi_injective : Function.Injective (Phi G B' B Y X) := by
  intro F1 F2 h
  apply WreathProduct.ext
  · funext x
    apply WreathProduct.ext
    · funext y
      exact congrArg (fun w => WreathProduct.func w (y, x)) h
    · exact congrArg (fun w => (WreathProduct.base w).func x) h
  · exact congrArg (fun w => (WreathProduct.base w).base) h

end WreathAssoc

/-- **Wreath associativity, up to division.**  `(G ≀_{B'} Y) ≀_X B` divides
    `G ≀_W (Y × X)` where the base `W = B' ≀_X B` acts on `Y × X` by
    `WreathAssoc.actW` (the inner base on the inner state, the outer base on the
    outer state).  Fully proved via the unscrambling embedding `WreathAssoc.Phi`
    (an injective semigroup homomorphism). -/
theorem sgDiv_wreath_assoc (G B' B Y X : Type u)
    [Monoid G] [Monoid B']
    [Monoid B]
    [MulAction B' Y] [MulAction B X] :
    letI := WreathAssoc.actW B' B Y X
    SgDiv (WreathProduct (WreathProduct G B' Y) B X)
          (WreathProduct G (WreathProduct B' B X) (Y × X)) := by
  let := WreathAssoc.actW B' B Y X
  exact sgDiv_of_injective_hom (sgDiv_refl _)
    (WreathAssoc.Phi G B' B Y X) (WreathAssoc.Phi_injective G B' B Y X)

/-- **Wreath product is monotone in the decoration factor.**  If `A` divides
    `A'`, then `A ≀_X B` divides `A' ≀_X B`: lift the surjection
    `U' ↠ A` pointwise over the decoration, restricting to the subsemigroup of
    `A' ≀_X B` whose decorations land in `U'`. -/
theorem sgDiv_wreath_decoration_mono (A A' B X : Type u) [Monoid A]
    [Monoid A'] [Monoid B] [MulAction B X]
    (h : SgDiv A A') :
    SgDiv (WreathProduct A B X) (WreathProduct A' B X) := by
  obtain ⟨U', φ', hφ'⟩ := h
  let U : Subsemigroup (WreathProduct A' B X) :=
    { carrier := {w | ∀ x, w.func x ∈ U'}
      mul_mem' := by
        rintro a b ha hb x
        rw [WreathProduct.mul_func]
        exact U'.mul_mem (ha _) (hb _) }
  refine ⟨U, ⟨fun w => ⟨fun x => φ' ⟨w.1.func x, w.2 x⟩, w.1.base⟩, ?_⟩, ?_⟩
  · rintro ⟨p, hp⟩ ⟨q, hq⟩
    apply WreathProduct.ext
    · funext x
      change φ' ⟨(p * q).func x, _⟩ = φ' ⟨p.func (q.base • x), _⟩ * φ' ⟨q.func x, _⟩
      rw [← φ'.map_mul]; congr 1
    · rfl
  · intro w
    choose g hg using fun x => hφ' (w.func x)
    refine ⟨⟨⟨fun x => (g x : A'), w.base⟩, fun x => (g x).2⟩, ?_⟩
    apply WreathProduct.ext
    · funext x
      change φ' ⟨(g x : A'), _⟩ = w.func x
      have : φ' (g x) = w.func x := hg x
      rw [← this]
    · rfl

/-- `SgDiv A PUnit` forces `A` to be a subsingleton (it is a quotient of a
    subsemigroup of the one-point monoid). -/
theorem subsingleton_of_sgDiv_punit (A : Type u) [Monoid A]
    (h : SgDiv A PUnit.{u + 1}) : Subsingleton A := by
  obtain ⟨U, φ, hφ⟩ := h
  constructor
  intro a b
  obtain ⟨ua, rfl⟩ := hφ a
  obtain ⟨ub, rfl⟩ := hφ b
  congr 1
  apply Subtype.ext
  apply Subsingleton.elim

/-- When the decoration factor `A` is a subsingleton, `A ≀_X B ≅ B`, so `A ≀_X B`
    divides `B` (the projection onto the base is an isomorphism). -/
theorem sgDiv_wreath_of_subsingleton_decoration (A B X : Type u) [Monoid A]
    [Monoid B] [MulAction B X] [Subsingleton A] :
    SgDiv (WreathProduct A B X) B := by
  refine ⟨⊤, ⟨fun b => ⟨fun _ => 1, b.1⟩, ?_⟩, ?_⟩
  · rintro ⟨a, -⟩ ⟨b, -⟩
    apply WreathProduct.ext
    · funext x; exact Subsingleton.elim _ _
    · rfl
  · intro w
    refine ⟨⟨w.base, Subsemigroup.mem_top _⟩, ?_⟩
    apply WreathProduct.ext
    · funext x; exact Subsingleton.elim _ _
    · rfl

/-- **The factor-tower concatenation step.**

    If `S` divides `A ≀_X B`, the decoration factor `A` has a factor tower
    `towA`, and the base factor `B` has a factor tower `towB`, then `S` has the
    *concatenated* factor tower `towA ++ towB`.

    It flattens the two sub-decompositions into one explicit list.  The proof is by
    induction on `towA`, using `sgDiv_wreath_decoration_mono` to push the
    decomposition of `A` into the decoration slot and `sgDiv_wreath_assoc` to
    re-associate the nested wreath into the base. -/
theorem divTowerWreath_wreathStep :
    ∀ (towA : List KRFactor.{u}) {S A B X : Type u}
      [Monoid S] [Finite S] [Monoid A] [Finite A] [Monoid B] [Finite B]
      [Finite X] [MulAction B X],
      SgDiv S (WreathProduct A B X) → DivTowerWreath A towA →
      ∀ {towB : List KRFactor.{u}}, DivTowerWreath B towB →
        DivTowerWreath S (towA ++ towB) := by
  intro towA
  induction towA with
  | nil =>
      intro S A B X _ _ _ _ _ _ _ _ hdiv hA towB hB
      let := Fintype.ofFinite X
      rw [divTowerWreath_nil] at hA
      have : Subsingleton A := subsingleton_of_sgDiv_punit A hA
      have hSB : SgDiv S B :=
        sgDiv_trans hdiv
          (sgDiv_wreath_of_subsingleton_decoration A B X)
      simpa using divTowerWreath_of_sgDiv hSB hB
  | cons F rest IH =>
      intro S A B X _ _ _ _ _ _ _ _ hdiv hA towB hB
      let := Fintype.ofFinite X
      rw [divTowerWreath_cons] at hA
      obtain ⟨B', mB', fB', Y', fY', aY', hB'rest, hAdiv⟩ := hA
      rw [List.cons_append, divTowerWreath_cons]
      -- The new base is the wreath `B' ≀_X B` (using the *outer* state `X`), acting
      -- on the product state `Y' × X` via `WreathAssoc.actW`.
      have : Fintype B' := Fintype.ofFinite B'
      let := WreathAssoc.actW B' B Y' X
      refine ⟨WreathProduct B' B X, inferInstance, inferInstance,
        Y' × X, inferInstance, WreathAssoc.actW B' B Y' X, ?_, ?_⟩
      · -- The base `B' ≀_X B` decomposes via `rest ++ towB` by the IH at `rest`:
        -- `B' ≀_X B  ≼  B' ≀_X B` (reflexivity), `B'` decomposes via `rest`,
        -- `B` via `towB`.
        exact IH (S := WreathProduct B' B X) (A := B') (B := B) (X := X)
          (sgDiv_refl _) hB'rest hB
      · -- The head SgDiv: push `A ≼ F.carrier ≀_{B'} Y'` into the decoration, then
        -- re-associate `(F.carrier ≀_{B'} Y') ≀_X B  ≼  F.carrier ≀_{B'≀_X B} (Y'×X)`.
        have h1 : SgDiv (WreathProduct A B X)
            (WreathProduct (WreathProduct F.carrier B' Y') B X) :=
          sgDiv_wreath_decoration_mono A (WreathProduct F.carrier B' Y') B X hAdiv
        have h2 : SgDiv (WreathProduct (WreathProduct F.carrier B' Y') B X)
            (WreathProduct F.carrier (WreathProduct B' B X) (Y' × X)) :=
          sgDiv_wreath_assoc F.carrier B' B Y' X
        exact sgDiv_trans hdiv
          (sgDiv_trans h1 h2)

/-! ## Factor towers whose factors divide the monoid

`KRFactorTowerSub M` is a factor tower of `M` in which every factor divides `M`. For finite
groups such a tower is built by induction along a normal subgroup
(`group_subquotient_faithful_aux`); the main theorem uses it in its group case.
-/

open Green

/-! ### Monoid-division helpers -/

/-- A surjective monoid homomorphism `φ : M ↠ N` exhibits `N` as a quotient of
    `M`, hence `N` divides `M`. -/
theorem monoidDivides_of_surjective {M N : Type u} [Monoid M] [Monoid N]
    (φ : M →* N) (hφ : Function.Surjective φ) :
    MonoidDivides N M :=
  ⟨⊤, φ.comp (⊤ : Submonoid M).subtype, fun n => by
    obtain ⟨m, rfl⟩ := hφ n; exact ⟨⟨m, Submonoid.mem_top m⟩, rfl⟩⟩

/-- Monoid division is reflexive. -/
theorem monoidDivides_refl (M : Type u) [Monoid M] :
    MonoidDivides M M :=
  monoidDivides_of_surjective (MonoidHom.id M) Function.surjective_id

/-- A subgroup `N ≤ G` divides `G`. -/
theorem monoidDivides_subgroup {G : Type u} [Group G] (N : Subgroup G) :
    MonoidDivides (N : Type u) G :=
  ⟨N.toSubmonoid, MonoidHom.id _, fun x => ⟨x, rfl⟩⟩

/-- The quotient group `G/N` divides `G`. -/
theorem quotientGroup_divides {G : Type u} [Group G] (N : Subgroup G) [N.Normal] :
    MonoidDivides (G ⧸ N) G :=
  monoidDivides_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-! ### The subquotient-faithful factor tower -/

/-- `SubFactorsDivide M factors` asserts every factor's carrier divides `M`. -/
@[expose]
def SubFactorsDivide (M : Type u) [Monoid M] (factors : List KRFactor.{u}) : Prop :=
  ∀ F ∈ factors, MonoidDivides F.carrier M

theorem subFactorsDivide_nil (M : Type u) [Monoid M] :
    SubFactorsDivide M ([] : List KRFactor.{u}) := by
  intro F hF; exact absurd hF (List.not_mem_nil)

theorem subFactorsDivide_single {M : Type u} [Monoid M] (F : KRFactor.{u})
    (h : MonoidDivides F.carrier M) :
    SubFactorsDivide M [F] := by
  intro G hG; rw [List.mem_singleton] at hG; subst hG; exact h

/-- If every factor of `factors` divides `A`, and `A` divides `M`, then every
    factor divides `M` (transitivity of division). -/
theorem subFactorsDivide_of_divides {A M : Type u} [Monoid A] [Monoid M]
    (hAM : MonoidDivides A M)
    {factors : List KRFactor.{u}} (h : SubFactorsDivide A factors) :
    SubFactorsDivide M factors :=
  fun F hF => (h F hF).trans hAM

/-- The append of two divides-witnessed factor lists. -/
theorem subFactorsDivide_append {M : Type u} [Monoid M]
    {towA towB : List KRFactor.{u}}
    (hA : SubFactorsDivide M towA) (hB : SubFactorsDivide M towB) :
    SubFactorsDivide M (towA ++ towB) := by
  intro F hF
  rcases List.mem_append.mp hF with h | h
  · exact hA F h
  · exact hB F h

/-- **A factor tower whose factors divide `M`.**  A factor list, a proof that `M`
    has the recursive wreath-division tower, and the guarantee that every
    factor's carrier divides `M`. -/
structure KRFactorTowerSub (M : Type u) [Monoid M] [Finite M] where
  /-- The explicit list of Krohn-Rhodes factors. -/
  factors : List KRFactor.{u}
  /-- The recursive wreath-division tower for `M` over `factors`. -/
  divides : DivTowerWreath M factors
  /-- Every factor's carrier divides `M` (the subquotient-faithful condition). -/
  factorsDivide : SubFactorsDivide M factors

/-! ### Subquotient-faithful Krohn-Rhodes for finite groups -/

/-- **Subquotient-faithful Krohn-Rhodes for finite groups.** Every finite group
    `G` has a subquotient-faithful factor tower: simple-group factors, each
    dividing `G`, together with a recursive wreath-division tower for `G`.  Proved by strong
    induction on `Nat.card G`, peeling a proper normal subgroup `N` and recursing
    on the subgroup `↥N` (`÷ G`) and the quotient `G/N` (`÷ G`), threading the
    `MonoidDivides`-to-`G` witness through every factor (subgroup-divides /
    quotient-divides + transitivity). -/
theorem group_subquotient_faithful_aux (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G ≤ n →
      Nonempty (KRFactorTowerSub G) := by
  classical
  induction n with
  | zero =>
    intro G _ _ hcard
    have : 0 < Nat.card G := Nat.card_pos
    omega
  | succ k IH =>
    intro G _ _ hcard
    by_cases hss : Subsingleton G
    · exact ⟨⟨[], divTowerWreath_nil_of_subsingleton G, subFactorsDivide_nil G⟩⟩
    have hnontriv : Nontrivial G := not_subsingleton_iff_nontrivial.mp hss
    by_cases hsimple : IsSimpleGroup G
    · refine ⟨⟨[KRFactor.ofSimpleGroup G], divTowerWreath_ofSimpleGroup G, ?_⟩⟩
      exact subFactorsDivide_single _ (monoidDivides_refl (KRFactor.ofSimpleGroup G).carrier)
    · -- `G` not simple: peel a proper nontrivial normal subgroup.
      have hex : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
        by_contra hne
        push Not at hne
        apply hsimple
        refine ⟨fun H hH => ?_⟩
        by_cases h1 : H = ⊥
        · exact Or.inl h1
        · exact Or.inr (hne H hH h1)
      obtain ⟨N, hNnormal, hNbot, hNtop⟩ := hex
      have : N.Normal := hNnormal
      obtain ⟨hcardN, hcardQ⟩ :
          Nat.card N < Nat.card G ∧ Nat.card (G ⧸ N) < Nat.card G := by
        have hmul : Nat.card (G ⧸ N) * Nat.card N = Nat.card G := by
          rw [← Subgroup.index_eq_card]; exact N.index_mul_card
        have hN_pos : 0 < Nat.card N := Nat.card_pos
        have hQ_pos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
        have hN_ne_one : Nat.card N ≠ 1 := by
          intro hN; apply hNbot
          have : Subsingleton N := by
            rw [Nat.card_eq_one_iff_unique] at hN; exact hN.1
          exact Subgroup.eq_bot_of_subsingleton (H := N)
        have hQ_ne_one : Nat.card (G ⧸ N) ≠ 1 := by
          intro hQ; apply hNtop
          have hindex : N.index = 1 := by rw [Subgroup.index_eq_card]; exact hQ
          exact Subgroup.index_eq_one.mp hindex
        have hN_ge : 2 ≤ Nat.card N := by omega
        have hQ_ge : 2 ≤ Nat.card (G ⧸ N) := by omega
        constructor
        · simpa only [one_mul, hmul] using Nat.mul_lt_mul_of_pos_right hQ_ge hN_pos
        · simpa only [mul_one, hmul] using Nat.mul_lt_mul_of_pos_left hN_ge hQ_pos
      have hN_le : Nat.card (N : Type u) ≤ k := by omega
      have hQ_le : Nat.card (G ⧸ N) ≤ k := by omega
      obtain ⟨towN⟩ := IH (N : Type u) hN_le
      obtain ⟨towQ⟩ := IH (G ⧸ N) hQ_le
      have : Fintype (G ⧸ N) := Fintype.ofFinite _
      have hdiv : SgDiv G (WreathProduct (N : Type u) (G ⧸ N) (G ⧸ N)) :=
        group_sgdiv_via_normal N
      refine ⟨⟨towN.factors ++ towQ.factors, ?_, ?_⟩⟩
      · exact divTowerWreath_wreathStep towN.factors hdiv towN.divides towQ.divides
      · apply subFactorsDivide_append
        · exact subFactorsDivide_of_divides (monoidDivides_subgroup N) towN.factorsDivide
        · exact subFactorsDivide_of_divides (quotientGroup_divides N) towQ.factorsDivide

end LeanPool.KrohnRhodes
