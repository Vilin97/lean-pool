/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LocalEMCompression
import LeanPool.InfinitaryLogic.Methods.HighlyOrderTransitive
/-!
# Tuple codes and orbit classification (issue #11 unit 3b)

Every finite tuple of local EM carrier elements is coded by choosing (noncomputably, and with
no canonicity claim) quotient representatives, taking the union of their finite skeleton
supports, and compressing each representative against that common support
(`LocalEMContext.tupleCode`). The code forgets the actual `J`-values of the support while
retaining the term shapes and the equality/order pattern — so the code type is the countable
`LocalEMTupleCode Λ n` (`LocalEMCompression.lean`).

The decisive endpoint is `exists_carrierEquiv_of_tupleCode_eq`: over a highly order-transitive
skeleton, EQUAL CODES IMPLY THE SAME AUTOMORPHISM ORBIT — an order automorphism carrying the
first support's increasing enumeration to the second's (high transitivity) renames the first
tuple's representatives into the second's (`locJRename_expand` between the two expansions),
and descends to the induced structure automorphism (`carrierEquiv_mkClass`). The code is NOT
invariant under changing representatives, and need not be: distinguishing equivalent tuples
only creates more codes, and countability plus "same code ⇒ same orbit" is all the
countably-many-types argument consumes.
-/

namespace FirstOrder

namespace Language

variable {Λ : Language.{0, 0}} {J : Type} [LinearOrder J] {M : Type} [Λ.Structure M]

/-- The common finite skeleton support of a tuple's chosen representatives. -/
private noncomputable def LocalEMContext.tupleSupport (ctx : LocalEMContext Λ J (M := M)) {n : ℕ}
    (a : Fin n → ctx.Carrier) : Finset J :=
  Finset.univ.biUnion fun i => locJSupport Λ J (Quotient.out (a i))

private theorem LocalEMContext.locJSupport_out_subset_tupleSupport
    (ctx : LocalEMContext Λ J (M := M)) {n : ℕ} (a : Fin n → ctx.Carrier) (i : Fin n) :
    locJSupport Λ J (Quotient.out (a i)) ⊆ ctx.tupleSupport a :=
  Finset.subset_biUnion_of_mem (fun i => locJSupport Λ J (Quotient.out (a i)))
    (Finset.mem_univ i)

/-- **The tuple code**: representatives compressed against their common support. Noncanonical
(it depends on `Quotient.out`), but countable and orbit-complete — which is all that is
needed. -/
noncomputable def LocalEMContext.tupleCode (ctx : LocalEMContext Λ J (M := M)) {n : ℕ}
    (a : Fin n → ctx.Carrier) : LocalEMTupleCode Λ n :=
  ⟨(ctx.tupleSupport a).card, fun i =>
    locJCompress Λ J (ctx.tupleSupport a) (Quotient.out (a i))
      (ctx.locJSupport_out_subset_tupleSupport a i)⟩

/-- **The orbit theorem**: over a highly order-transitive skeleton, tuples with equal codes lie
in the same orbit of the induced structure automorphisms — some order automorphism of `J`
carries one tuple to the other through the descended equivalence. -/
theorem LocalEMContext.exists_carrierEquiv_of_tupleCode_eq
    (ctx : LocalEMContext Λ J (M := M)) (hJ : HighlyOrderTransitive J) {n : ℕ}
    {a b : Fin n → ctx.Carrier} (h : ctx.tupleCode a = ctx.tupleCode b) :
    ∃ e : J ≃o J, ∀ i, ctx.carrierEquiv e (a i) = b i := by
  have hk : (ctx.tupleSupport a).card = (ctx.tupleSupport b).card := congrArg Sigma.fst h
  obtain ⟨e, he⟩ := hJ (ctx.tupleSupport a).card
    ((ctx.tupleSupport a).orderEmbOfFin rfl)
    ((ctx.tupleSupport b).orderEmbOfFin hk.symm)
  refine ⟨e, fun i => ?_⟩
  -- expanding both codes along the SECOND support's enumeration agrees componentwise
  have hcode := congrArg (fun c : LocalEMTupleCode Λ n =>
    if hc : (ctx.tupleSupport b).card = c.1 then
      some (fun i => locJExpand Λ J ((ctx.tupleSupport b).orderEmbOfFin hc) (c.2 i))
    else none) h
  -- Both `dite`s are discharged in term mode. `(ctx.tupleCode _).fst` projects out of a
  -- semireducible `def`, so the branch conditions are not type-correct at `implicit`
  -- transparency; neither `simp only [tupleCode]` nor `rw [dite_eq_left]` can act on them
  -- in place, whereas `Eq.trans` elaborates at default transparency.
  have hexp : (some fun i => locJExpand Λ J ((ctx.tupleSupport b).orderEmbOfFin hk.symm)
        (locJCompress Λ J (ctx.tupleSupport a) (Quotient.out (a i))
          (ctx.locJSupport_out_subset_tupleSupport a i)))
      = some fun i => locJExpand Λ J ((ctx.tupleSupport b).orderEmbOfFin rfl)
          (locJCompress Λ J (ctx.tupleSupport b) (Quotient.out (b i))
            (ctx.locJSupport_out_subset_tupleSupport b i)) :=
    (dite_eq_left hk.symm).symm.trans (hcode.trans (dite_eq_left rfl))
  have hcomp : locJExpand Λ J ((ctx.tupleSupport b).orderEmbOfFin hk.symm)
      (locJCompress Λ J (ctx.tupleSupport a) (Quotient.out (a i))
        (ctx.locJSupport_out_subset_tupleSupport a i))
      = Quotient.out (b i) := by
    have hBi := congrFun (Option.some.inj hexp) i
    exact hBi.trans (locJExpand_compress Λ J (ctx.tupleSupport b) (Quotient.out (b i))
      (ctx.locJSupport_out_subset_tupleSupport b i))
  have hterm : locJRename Λ J e (Quotient.out (a i)) = Quotient.out (b i) := by
    conv_lhs => rw [← locJExpand_compress Λ J (ctx.tupleSupport a) (Quotient.out (a i))
      (ctx.locJSupport_out_subset_tupleSupport a i)]
    rw [locJRename_expand Λ J e _ _ he]
    exact hcomp
  calc ctx.carrierEquiv e (a i)
      = ctx.carrierEquiv e (ctx.mkClass (t := Quotient.out (a i))) :=
        congrArg _ (Quotient.out_eq (a i)).symm
    _ = ctx.mkClass (t := locJRename Λ J e (Quotient.out (a i))) :=
        ctx.carrierEquiv_mkClass e (Quotient.out (a i))
    _ = ctx.mkClass (t := Quotient.out (b i)) := by rw [hterm]
    _ = b i := Quotient.out_eq (b i)

end Language

end FirstOrder
