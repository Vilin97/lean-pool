/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LocalEMTupleOrbit
import LeanPool.InfinitaryLogic.ModelTheory.InfinitaryTypes
/-!
# Smallness of the local EM model (issue #11 unit 4)

The conditional countability theorem: over a highly order-transitive skeleton and a countable
base language, the local EM carrier realizes only countably many complete `L_{ω₁ω}`-types at
every arity (`LocalEMContext.lomega1omegaSmall`), for the rich `localColim`-reduct structure
`structureBase`.

The argument avoids any orbit quotient, via code FIBERS: for each tuple code `c`, `CodeTypes c`
is the set of realized types of tuples with code `c`. The orbit theorem plus formula invariance
under the induced automorphisms make each fiber SUBSINGLETON (`codeTypes_subsingleton`), the
realized types are exactly the union of the fibers over the countable code type
(`realizedTypes_eq_iUnion_codeTypes` — set extensionality), and a countable union of
subsingletons is countable. Transport to the original language is `Lomega1omegaSmall.of_expansion`
(`ModelTheory/InfinitaryTypes.lean`), not re-proved here.
-/

namespace FirstOrder

namespace Language

variable {Λ : Language.{0, 0}} {J : Type} [LinearOrder J] {M : Type} [Λ.Structure M]

/-- The fiber of realized types over a tuple code: the types of tuples whose code is `c`. -/
private def LocalEMContext.CodeTypes (ctx : LocalEMContext Λ J (M := M)) {n : ℕ}
    (c : LocalEMTupleCode Λ n) : Set (Set (Λ.BoundedFormulaω Empty n)) :=
  letI := ctx.structureBase
  {p | ∃ a : Fin n → ctx.Carrier, ctx.tupleCode a = c ∧ infinitaryType ctx.Carrier a = p}

/-- **Each code fiber is subsingleton**: tuples with the same code lie in one orbit of the
induced automorphisms (`exists_carrierEquiv_of_tupleCode_eq`), and every infinitary formula is
invariant under those automorphisms (`realize_carrierEquiv`), so they realize the same type. -/
private theorem LocalEMContext.codeTypes_subsingleton (ctx : LocalEMContext Λ J (M := M))
    (hJ : HighlyOrderTransitive J) {n : ℕ} (c : LocalEMTupleCode Λ n) :
    (ctx.CodeTypes c).Subsingleton := by
  let := ctx.structureBase
  rintro p ⟨a, ha, rfl⟩ q ⟨b, hb, rfl⟩
  obtain ⟨e, he⟩ := ctx.exists_carrierEquiv_of_tupleCode_eq hJ (ha.trans hb.symm)
  ext ψ
  show ψ.Realize Empty.elim a ↔ ψ.Realize Empty.elim b
  have h1 := ctx.realize_carrierEquiv e ψ Empty.elim a
  rwa [show (⇑(ctx.carrierEquiv e) ∘ Empty.elim : Empty → ctx.Carrier) = Empty.elim from
      funext fun x => x.elim,
    show ⇑(ctx.carrierEquiv e) ∘ a = b from funext he] at h1

/-- **The realized types are the union of the code fibers** — set extensionality. -/
private theorem LocalEMContext.realizedTypes_eq_iUnion_codeTypes (ctx : LocalEMContext Λ J (M := M))
    (n : ℕ) :
    letI := ctx.structureBase
    RealizedInfinitaryTypes (L := Λ) ctx.Carrier n
      = ⋃ c : LocalEMTupleCode Λ n, ctx.CodeTypes c := by
  let := ctx.structureBase
  ext p
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨ctx.tupleCode a, a, rfl, rfl⟩
  · rintro ⟨c, a, _, rfl⟩
    exact ⟨a, rfl⟩

/-- **The conditional smallness theorem** (issue #11 unit 4): over a highly order-transitive
skeleton and a countable base language, the local EM carrier — with its rich `localColim`-reduct
structure — realizes only countably many complete `L_{ω₁ω}`-types at every arity. -/
theorem LocalEMContext.lomega1omegaSmall (ctx : LocalEMContext Λ J (M := M))
    (hJ : HighlyOrderTransitive J) [Countable (Σ l, Λ.Functions l)] :
    letI := ctx.structureBase
    Lomega1omegaSmall (L := Λ) ctx.Carrier := by
  let := ctx.structureBase
  intro n
  have hunion := ctx.realizedTypes_eq_iUnion_codeTypes n
  rw [hunion]
  have : Countable (LocalEMTupleCode Λ n) := countable_localEMTupleCode Λ n
  exact Set.countable_iUnion fun c => (ctx.codeTypes_subsingleton hJ c).countable

end Language

end FirstOrder
