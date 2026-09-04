/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LocalEMCompression
import LeanPool.InfinitaryLogic.ModelTheory.HanfSpectrum.CardinalBounds
/-!
# Exact cardinality of the local EM carrier (issue #11 unit 5)

The orbit code (`LocalEMTupleOrbit.lean`) deliberately forgets the `J`-locations of supports —
so it cannot bound the carrier. The **located** term code restores them:
`LocatedTermCode Λ J := Σ k, (Fin k ↪o J) × Λ[[Fin k]].Term Empty` — a compression arity, the
increasing enumeration of the representative's support, and the compressed term. Since the
embedding travels WITH the code, expansion is a total function (`LocatedTermCode.expand`), and
`locJExpand_compress` makes the element-to-code map injective (`locatedCode_injective`).

* Upper bound (`mk_carrier_le`): compressed terms are countable (countable base language),
  `Fin k ↪o J` injects into `Fin k → J`, each finite power is at most `max ℵ₀ #J`, and the
  countable sigma stays there (`CardinalBounds.mk_sigma_le_of_countable`).
* Lower bound (`mk_le_mk_carrier`): for an INJECTIVE deep sequence the skeleton classes
  `[c_j]` are pairwise distinct — `LocalEMEq` on two constants would force the deep sequence
  to repeat at distinct ranks.
* **Exact cardinality** (`mk_carrier`): `mk ctx.Carrier = max ℵ₀ (mk J)` for infinite `J`,
  countable base language, injective deep sequence.
-/

namespace FirstOrder

namespace Language

variable (Λ : Language.{0, 0}) (J : Type) [LinearOrder J]

/-- The located term code: compression arity, the support's increasing enumeration, and the
compressed term. Unlike the orbit code, it remembers WHERE the support sits in `J`. -/
private def LocatedTermCode : Type :=
  Σ k : ℕ, (Fin k ↪o J) × Λ[[Fin k]].Term Empty

/-- Expansion of a located code — total, since the embedding travels with the code. -/
def LocatedTermCode.expand : LocatedTermCode Λ J → Λ[[J]].Term Empty
  | ⟨_, s, u⟩ => locJExpand Λ J s u

variable {Λ J} {M : Type} [Λ.Structure M]

/-- The located code of a carrier element: enumerate its representative's support and
compress. -/
private noncomputable def LocalEMContext.locatedCode (ctx : LocalEMContext Λ J (M := M))
    (x : ctx.Carrier) : LocatedTermCode Λ J :=
  ⟨(locJSupport Λ J (Quotient.out x)).card,
    ((locJSupport Λ J (Quotient.out x)).orderEmbOfFin rfl,
      locJCompress Λ J (locJSupport Λ J (Quotient.out x)) (Quotient.out x) (subset_refl _))⟩

private theorem LocalEMContext.expand_locatedCode (ctx : LocalEMContext Λ J (M := M))
    (x : ctx.Carrier) : (ctx.locatedCode x).expand = Quotient.out x :=
  locJExpand_compress Λ J _ (Quotient.out x) (subset_refl _)

/-- **The located code is injective**: equal codes expand to equal representatives, hence equal
classes. -/
private theorem LocalEMContext.locatedCode_injective (ctx : LocalEMContext Λ J (M := M)) :
    Function.Injective ctx.locatedCode := by
  intro x y hxy
  have h := (ctx.expand_locatedCode x).symm.trans
    ((congrArg (LocatedTermCode.expand Λ J) hxy).trans (ctx.expand_locatedCode y))
  rw [← Quotient.out_eq x, ← Quotient.out_eq y, h]

/-! ## The upper bound -/

/-- The located-code type has size at most `max ℵ₀ #J` for a countable base language. -/
private theorem mk_locatedTermCode_le [Countable (Σ l, Λ.Functions l)] :
    Cardinal.mk (LocatedTermCode Λ J) ≤ max Cardinal.aleph0 (Cardinal.mk J) := by
  have hcnt : ∀ k, Countable (Λ[[Fin k]].Term Empty) := fun k =>
    haveI := countable_sigma_functions_withFin Λ k
    inferInstance
  show Cardinal.mk (Σ k : ℕ, (Fin k ↪o J) × Λ[[Fin k]].Term Empty)
    ≤ max Cardinal.aleph0 (Cardinal.mk J)
  refine FirstOrder.HanfLadder.mk_sigma_le_of_countable (le_max_left _ _) fun k => ?_
  have h1 : Cardinal.mk ((Fin k ↪o J) × Λ[[Fin k]].Term Empty)
      ≤ Cardinal.mk (Fin k ↪o J) * Cardinal.aleph0 := by
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    exact mul_le_mul_right (Cardinal.mk_le_aleph0 (α := Λ[[Fin k]].Term Empty)) _
  have h2 : Cardinal.mk (Fin k ↪o J) ≤ Cardinal.mk (Fin k → J) :=
    Cardinal.mk_le_of_injective (fun s t hst => by
      exact DFunLike.coe_injective hst)
  have h3 : Cardinal.mk (Fin k → J) ≤ max Cardinal.aleph0 (Cardinal.mk J) := by
    have hpow : Cardinal.mk (Fin k → J) = Cardinal.mk J ^ (k : Cardinal) := by
      rw [← Cardinal.power_def, Cardinal.mk_fin]
    rw [hpow]
    calc Cardinal.mk J ^ (k : Cardinal)
        ≤ (max Cardinal.aleph0 (Cardinal.mk J)) ^ (k : Cardinal) :=
          Cardinal.power_le_power_right (le_max_right _ _)
      _ ≤ max Cardinal.aleph0 (Cardinal.mk J) :=
          Cardinal.pow_le (le_max_left _ _) Cardinal.natCast_lt_aleph0
  calc Cardinal.mk ((Fin k ↪o J) × Λ[[Fin k]].Term Empty)
      ≤ Cardinal.mk (Fin k ↪o J) * Cardinal.aleph0 := h1
    _ ≤ max Cardinal.aleph0 (Cardinal.mk J) * max Cardinal.aleph0 (Cardinal.mk J) :=
        mul_le_mul' (h2.trans h3) (le_max_left _ _)
    _ = max Cardinal.aleph0 (Cardinal.mk J) :=
        Cardinal.mul_eq_self (le_max_left _ _)

/-- **The upper bound**: the carrier has size at most `max ℵ₀ #J`. -/
private theorem LocalEMContext.mk_carrier_le (ctx : LocalEMContext Λ J (M := M))
    [Countable (Σ l, Λ.Functions l)] :
    Cardinal.mk ctx.Carrier ≤ max Cardinal.aleph0 (Cardinal.mk J) :=
  (Cardinal.mk_le_of_injective ctx.locatedCode_injective).trans mk_locatedTermCode_le

/-! ## The lower bound -/

/-- **Distinct skeleton constants have distinct classes** for an injective deep sequence:
`LocalEMEq c_j c_{j'}` would force `a (d + r) = a (d + r')` at distinct ranks. -/
private theorem LocalEMContext.mkClass_const_injective (ctx : LocalEMContext Λ J (M := M))
    (hinj : Function.Injective ctx.a) :
    Function.Injective fun j : J =>
      ctx.mkClass (t := Term.func (Sum.inr j : Λ[[J]].Functions 0) Fin.elim0) := by
  intro j j' hjj'
  by_contra hne
  have heq : LocalEMEq Λ J ctx.a
      (Term.func (Sum.inr j : Λ[[J]].Functions 0) Fin.elim0)
      (Term.func (Sum.inr j' : Λ[[J]].Functions 0) Fin.elim0) := Quotient.exact hjj'
  obtain ⟨d, hd⟩ := heq.exists
  set S := locJSupport Λ J (Term.func (Sum.inr j : Λ[[J]].Functions 0) Fin.elim0)
    ∪ locJSupport Λ J (Term.func (Sum.inr j' : Λ[[J]].Functions 0) Fin.elim0) with hS
  have hd' : ctx.a (d + deepRank J S j) = ctx.a (d + deepRank J S j') := hd
  have hrank : deepRank J S j = deepRank J S j' := by
    have := hinj hd'
    omega
  have hjS : j ∈ S :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self j))
  have hj'S : j' ∈ S :=
    Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_singleton_self j'))
  rcases lt_trichotomy j j' with hlt | heq' | hlt
  · exact absurd hrank (ne_of_lt (deepRank_lt_of_lt J hjS hlt))
  · exact hne heq'
  · exact absurd hrank.symm (ne_of_lt (deepRank_lt_of_lt J hj'S hlt))

/-- **The lower bound**: the skeleton injects into the carrier. -/
private theorem LocalEMContext.mk_le_mk_carrier (ctx : LocalEMContext Λ J (M := M))
    (hinj : Function.Injective ctx.a) :
    Cardinal.mk J ≤ Cardinal.mk ctx.Carrier :=
  Cardinal.mk_le_of_injective (ctx.mkClass_const_injective hinj)

/-- **Exact carrier cardinality** (issue #11 unit 5): for an infinite skeleton, a countable
base language, and an injective deep sequence, `mk ctx.Carrier = max ℵ₀ (mk J)`. -/
theorem LocalEMContext.mk_carrier_eq (ctx : LocalEMContext Λ J (M := M))
    [Countable (Σ l, Λ.Functions l)] [Infinite J] (hinj : Function.Injective ctx.a) :
    Cardinal.mk ctx.Carrier = max Cardinal.aleph0 (Cardinal.mk J) := by
  refine le_antisymm ctx.mk_carrier_le (max_le ?_ (ctx.mk_le_mk_carrier hinj))
  exact le_trans (Cardinal.aleph0_le_mk J) (ctx.mk_le_mk_carrier hinj)

end Language

end FirstOrder
