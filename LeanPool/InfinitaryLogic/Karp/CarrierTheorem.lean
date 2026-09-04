/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Karp.PotentialIso
import LeanPool.InfinitaryLogic.Scott.AtomicDiagram
import LeanPool.InfinitaryLogic.Scott.BackAndForth
import LeanPool.InfinitaryLogic.Mathlib.ModelTheory.Infinitary.QuantifierRank
/-!
# Karp's theorem at a common branching carrier

Karp's theorem for the fixed-carrier infinitary syntax: two structures are potentially
isomorphic if and only if they satisfy the same `L∞ω` sentences.

The point of the fixed-carrier formulation is where the quantifier over index types lives.
In a syntax whose `iSup`/`iInf` nodes each carry their own index type, the theorem has to
quantify over index types *inside* every node, which forces the index universe to track the
structure universe. Here each formula branches over a single carrier `ι`, so the quantifier
sits outside the syntax, in `InfEquivW`, and the backward direction needs only **one**
carrier — any `κ` admitting codings of both structures.

## Main definitions

- `InfEquivAt L ι M N`: agreement on all `L∞ω` sentences branching over the carrier `ι`.
  The structures may live in different universes.
- `InfEquivW L M N`: agreement at every carrier in the structures' shared universe.

## Main results

- `karp_theorem_at`: potential isomorphism is equivalent to `InfEquivAt L κ M N` for **any**
  carrier `κ` admitting codings `IndexCoding M κ` and `IndexCoding N κ`.
- `karp_theorem_on_sum`: the canonical specialization at `κ := M ⊕ N`.
- `karp_theorem_w`: the packaged same-universe endpoint, `Nonempty (PotentialIso L M N) ↔
  InfEquivW L M N`. This is the public statement of Karp's theorem.

The separating conjunctions in the backward direction are `iInfAlong` along the two given
codings — a conjunction indexed by one structure's carrier, expressed at `κ`. That is the
whole content of "any common carrier suffices": the sum is canonical, not necessary.

## References

- Carol R. Karp, *Finite-quantifier equivalence*, in **The Theory of Models** (Addison,
  Henkin, Tarski, eds.), North-Holland, 1965, pp. 407–412. The theorem.
- Carol R. Karp, *Languages with Expressions of Infinite Length*, North-Holland, 1964 —
  the infinitary languages themselves.
- H. Jerome Keisler and Julia F. Knight, *Barwise: infinitary logic and admissible sets*,
  Bull. Symbolic Logic **10** (2004), 4–36, doi:10.2178/bsl/1080330272. Theorem 1.2.1 is
  the statement formalized here.

The common-carrier formulation with `IndexCoding` is this formalization's presentation, not
a statement made in those sources; the mathematics is Karp's.
-/

universe u v w w' uι uκ

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {ι : Type uι} {κ : Type uκ}

open FirstOrder Structure BoundedFormulaInf

/-! ### Equivalence at a carrier -/

/-- `L∞ω`-equivalence at a fixed branching carrier `ι`: the structures satisfy the same
sentences whose infinitary connectives branch over `ι`. The structures need not share a
universe. -/
def InfEquivAt (L : Language.{u, v}) (ι : Type uι) (M : Type w) (N : Type w')
    [L.Structure M] [L.Structure N] : Prop :=
  ∀ φ : L.SentenceInf ι, SentenceInf.Realize φ M ↔ SentenceInf.Realize φ N

/-- `L∞ω`-equivalence with branching carriers drawn from the structures' own universe. The
quantifier over index types is here, outside the syntax, rather than inside every
infinitary node. -/
def InfEquivW (L : Language.{u, v}) (M N : Type w) [L.Structure M] [L.Structure N] : Prop :=
  ∀ ι : Type w, InfEquivAt L ι M N



section KarpAtCarrier

variable [L.IsRelational] {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- In a relational language every term is a variable. -/
private theorem term_eq_var {γ : Type*} (t : L.Term γ) : ∃ x, t = Term.var x := by
  cases t with
  | var x => exact ⟨x, rfl⟩
  | func f _ => exact (IsEmpty.false f).elim

/-- The atomic formula of an `AtomicIdx`, with the tuple in **bound** positions, generic in
the branching carrier.

Bound positions are what let the `all` case below consume `forth`/`back` directly: no
free-variable relabeling operation appears anywhere in this development. -/
private def atomicFormulaInf (idx : L.AtomicIdx n) : L.BoundedFormulaInf ι Empty n :=
  match idx with
  | .eq i j => .equal (.var (.inr i)) (.var (.inr j))
  | .rel R f => .rel R fun k => .var (.inr (f k))

omit [L.IsRelational] in
private theorem realize_atomicFormulaInf {P : Type w} [L.Structure P] (idx : L.AtomicIdx n)
    (xs : Fin n → P) :
    (atomicFormulaInf (ι := ι) idx).Realize Empty.elim xs ↔ idx.holds xs := by
  cases idx with
  | eq i j => simp [atomicFormulaInf, AtomicIdx.holds, Term.realize]
  | rel R f =>
    simp only [atomicFormulaInf, realize_rel, Term.realize, Sum.elim_inr, AtomicIdx.holds]
    exact Iff.rfl

/-- **Forward direction, generic in the carrier and its universe**: a potential isomorphism
forces agreement on every formula over every carrier `ι`. -/
private theorem potentialIso_agree_aux (P : PotentialIso L M N) :
    ∀ {k : ℕ} (φ : L.BoundedFormulaInf ι Empty k) (xs : Fin k → M) (ys : Fin k → N),
      (⟨k, xs, ys⟩ : Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ P.family →
      (φ.Realize Empty.elim xs ↔ φ.Realize Empty.elim ys) := by
  intro k φ
  induction φ with
  | falsum => intro xs ys _; simp
  | equal t₁ t₂ =>
    intro xs ys hmem
    obtain ⟨x₁, rfl⟩ := term_eq_var t₁
    obtain ⟨x₂, rfl⟩ := term_eq_var t₂
    rcases x₁ with e | i; · exact e.elim
    rcases x₂ with e | j; · exact e.elim
    simp only [realize_equal, Term.realize, Sum.elim_inr]
    exact (P.compatible _ hmem) (.eq i j)
  | rel R ts =>
    intro xs ys hmem
    have hvar : ∀ i, ∃ j, ts i = Term.var (Sum.inr j) := by
      intro i
      obtain ⟨x, hx⟩ := term_eq_var (ts i)
      rcases x with e | j
      · exact e.elim
      · exact ⟨j, hx⟩
    choose f hf using hvar
    simp only [realize_rel, hf, Term.realize, Sum.elim_inr]
    exact (P.compatible _ hmem) (.rel R f)
  | imp φ ψ ihφ ihψ =>
    intro xs ys hmem
    exact imp_congr (ihφ xs ys hmem) (ihψ xs ys hmem)
  | all φ ih =>
    intro xs ys hmem
    simp only [realize_all]
    constructor
    · intro hAll y
      obtain ⟨m, hm⟩ := P.back ⟨_, xs, ys⟩ hmem y
      exact (ih (Fin.snoc xs m) (Fin.snoc ys y) hm).mp (hAll m)
    · intro hAll m
      obtain ⟨y, hy⟩ := P.forth ⟨_, xs, ys⟩ hmem m
      exact (ih (Fin.snoc xs m) (Fin.snoc ys y) hy).mpr (hAll y)
  | iSup φs ih =>
    intro xs ys hmem
    exact exists_congr fun i => ih i xs ys hmem
  | iInf φs ih =>
    intro xs ys hmem
    exact forall_congr' fun i => ih i xs ys hmem

/-- **Forward direction**: a potential isomorphism yields agreement at every carrier, in
every index universe. -/
theorem PotentialIso.infEquivAt (P : PotentialIso L M N) (ι : Type uι) : InfEquivAt L ι M N :=
  fun φ => potentialIso_agree_aux P φ Fin.elim0 Fin.elim0 P.empty_mem

/-- **Backward direction at any common carrier**: agreement in a *single* carrier `κ`
admitting codings of both structures already builds a potential isomorphism.

The separating formula is an `iInfAlong` — a conjunction indexed by one structure's carrier,
expressed at `κ` along the given coding — closed by `ex`. The sum carrier plays no role. -/
private theorem infEquivAt_implies_potentialIso (cM : IndexCoding M κ) (cN : IndexCoding N κ)
    (h : InfEquivAt L κ M N) :
    Nonempty (PotentialIso L M N) := by
  refine ⟨{
    family := { p : Σ n : ℕ, (Fin n → M) × (Fin n → N) |
      ∀ φ : L.BoundedFormulaInf κ Empty p.1,
        φ.Realize Empty.elim p.2.1 ↔ φ.Realize Empty.elim p.2.2 }
    empty_mem := fun φ => h φ
    compatible := ?_
    forth := ?_
    back := ?_ }⟩
  · -- compatible: atomic formulas in bound positions detect atomic type
    intro p hp idx
    exact (realize_atomicFormulaInf idx p.2.1).symm.trans
      ((hp _).trans (realize_atomicFormulaInf idx p.2.2))
  · -- forth: contradiction via an `N`-indexed conjunction coded along `cN`
    rintro ⟨n, a, b⟩ hmem m
    by_contra h_no
    have h_no' : ∀ n' : N, ∃ φ : L.BoundedFormulaInf κ Empty (n + 1),
        ¬ (φ.Realize Empty.elim (Fin.snoc a m) ↔ φ.Realize Empty.elim (Fin.snoc b n')) := by
      intro n'
      by_contra hn
      refine h_no ⟨n', fun φ => ?_⟩
      by_contra hφ
      exact hn ⟨φ, hφ⟩
    choose φ_bad h_bad using h_no'
    have h_sep : ∀ n' : N, ∃ ψ : L.BoundedFormulaInf κ Empty (n + 1),
        ψ.Realize Empty.elim (Fin.snoc a m) ∧ ¬ ψ.Realize Empty.elim (Fin.snoc b n') := by
      intro n'
      by_cases hA : (φ_bad n').Realize Empty.elim (Fin.snoc a m)
      · exact ⟨φ_bad n', hA, fun hB => h_bad n' (iff_of_true hA hB)⟩
      · have hB : (φ_bad n').Realize Empty.elim (Fin.snoc b n') := by
          by_contra hB
          exact h_bad n' (iff_of_false hA hB)
        exact ⟨(φ_bad n').not, (realize_not).mpr hA, fun hc => (realize_not).mp hc hB⟩
    choose ψ hψ using h_sep
    set χ : L.BoundedFormulaInf κ Empty n := (iInfAlong cN ψ).ex with hχ
    have hM : χ.Realize Empty.elim a := by
      rw [hχ, realize_ex]
      exact ⟨m, by rw [realize_iInfAlong]; exact fun n' => (hψ n').1⟩
    have hN : ¬ χ.Realize Empty.elim b := by
      rw [hχ, realize_ex]
      rintro ⟨y, hy⟩
      rw [realize_iInfAlong] at hy
      exact (hψ y).2 (hy y)
    exact hN ((hmem χ).mp hM)
  · -- back: the mirror, via an `M`-indexed conjunction coded along `cM`
    rintro ⟨n, a, b⟩ hmem n'
    by_contra h_no
    have h_no' : ∀ m : M, ∃ φ : L.BoundedFormulaInf κ Empty (n + 1),
        ¬ (φ.Realize Empty.elim (Fin.snoc a m) ↔ φ.Realize Empty.elim (Fin.snoc b n')) := by
      intro m
      by_contra hn
      refine h_no ⟨m, fun φ => ?_⟩
      by_contra hφ
      exact hn ⟨φ, hφ⟩
    choose φ_bad h_bad using h_no'
    have h_sep : ∀ m : M, ∃ ψ : L.BoundedFormulaInf κ Empty (n + 1),
        ψ.Realize Empty.elim (Fin.snoc b n') ∧ ¬ ψ.Realize Empty.elim (Fin.snoc a m) := by
      intro m
      by_cases hB : (φ_bad m).Realize Empty.elim (Fin.snoc b n')
      · exact ⟨φ_bad m, hB, fun hA => h_bad m (iff_of_true hA hB)⟩
      · have hA : (φ_bad m).Realize Empty.elim (Fin.snoc a m) := by
          by_contra hA
          exact h_bad m (iff_of_false hA hB)
        exact ⟨(φ_bad m).not, (realize_not).mpr hB, fun hc => (realize_not).mp hc hA⟩
    choose ψ hψ using h_sep
    set χ : L.BoundedFormulaInf κ Empty n := (iInfAlong cM ψ).ex with hχ
    have hN : χ.Realize Empty.elim b := by
      rw [hχ, realize_ex]
      exact ⟨n', by rw [realize_iInfAlong]; exact fun m => (hψ m).1⟩
    have hM : ¬ χ.Realize Empty.elim a := by
      rw [hχ, realize_ex]
      rintro ⟨x, hx⟩
      rw [realize_iInfAlong] at hx
      exact (hψ x).2 (hx x)
    exact hM ((hmem χ).mpr hN)

/-- **Karp's theorem at any sufficiently large common carrier.**

Agreement in *one* carrier admitting codings of both structures already characterizes
potential isomorphism. The structures may live in different universes. -/
private theorem karp_theorem_at (cM : IndexCoding M κ) (cN : IndexCoding N κ) :
    Nonempty (PotentialIso L M N) ↔ InfEquivAt L κ M N :=
  ⟨fun ⟨P⟩ => P.infEquivAt _, infEquivAt_implies_potentialIso cM cN⟩

end KarpAtCarrier

section KarpCanonical

variable [L.IsRelational] {M N : Type w} [L.Structure M] [L.Structure N]

/-- **Karp's theorem at the sum carrier**: the canonical specialization of
`karp_theorem_at`, obtained by feeding it the two sum injections. -/
private theorem karp_theorem_on_sum :
    Nonempty (PotentialIso L M N) ↔ InfEquivAt L (M ⊕ N) M N :=
  karp_theorem_at (.sumInl M N) (.sumInr M N)

/-- **Karp's theorem** (Keisler–Knight 2004, Theorem 1.2.1): potential isomorphism is equivalent to
agreement on all `L∞ω` sentences branching over carriers in the structures' universe.

Forward instantiates the generic direction at each `ι`; backward specializes to the single
carrier `M ⊕ N`. Pure packaging around `karp_theorem_at`. -/
theorem karp_theorem_w :
    Nonempty (PotentialIso L M N) ↔ InfEquivW L M N :=
  ⟨fun ⟨P⟩ ι => P.infEquivAt ι,
   fun h => infEquivAt_implies_potentialIso (.sumInl M N) (.sumInr M N) (h (M ⊕ N))⟩

end KarpCanonical

/-! ### The quantifier-rank forward lemma

Back-and-forth equivalence at level `α` implies agreement on every formula of rank at most `α`.
This is stated at an arbitrary branching carrier, with independent structure universes, and
with `BFEquiv`'s ordinal in the *same* universe as `qrank` — so no `Ordinal.lift` enters the
induction. Callers whose ordinal genuinely lives elsewhere bridge at the boundary with
`BFEquiv.ofOrdinalLift` / `.toOrdinalLift`.

The tuple sits in free-variable positions here, because that is what the consumers need; the
`Fin.append` plumbing below is the cost of that choice, and is confined to these two lemmas. -/

section AgreementQR

variable [L.IsRelational] {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]



omit [L.IsRelational] in
/-- `Fin.snoc` distributes into `Fin.append` on the right component. -/
private theorem snoc_append_eq_append_snoc {γ : Type*} {n k : ℕ}
    (v : Fin n → γ) (xs : Fin k → γ) (x : γ) :
    Fin.snoc (Fin.append v xs) x = Fin.append v (Fin.snoc xs x) :=
  (Fin.append_snoc v xs x).symm





end AgreementQR

end Language

end FirstOrder
