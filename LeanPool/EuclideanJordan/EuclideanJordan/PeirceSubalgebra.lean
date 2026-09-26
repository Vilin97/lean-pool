/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.EuclideanJordan.EuclideanJordan.Class



/-!
# Peirce subalgebras: `J₂(c)` and `J₀(c)` as Euclidean Jordan algebras in their own right

`EuclideanJordan/Peirce.lean` carries the Peirce decomposition at a single idempotent as three
    *linear
maps* `peirceOne c`, `peirceHalf c`, `peirceZero c`, and `EuclideanJordan/PeirceMul.lean`
    carries the six
Faraut–Korányi rules governing how their images multiply.  Two of those rules —
`eigen_one_mul_one` and `eigen_zero_mul_zero` — say that the eigenvalue-`1` and eigenvalue-`0`
eigenspaces are closed under the product.  This file turns that closure into structure: each
of the two eigenspaces is itself a Euclidean Jordan algebra, with its own unit.

Everything that recurses into a Peirce subalgebra sits on this file.

## The subobject vehicle: `Submodule`, not `NonUnitalSubalgebra`

★ **This is a deviation from the build plan, and it is what made the module cheap.**  The plan
routed the two eigenspaces through `NonUnitalSubalgebra ℝ J` and priced the module at its
risk #3, on a probe showing that `IsCommJordan ↥S` does not synthesise for a
`NonUnitalSubalgebra` subtype: Mathlib has no such transfer instance, so one would have to be
written, and `IsFormallyReal` with it.

That probe reproduces here, re-run against this tree on 2026-08-22: with
`[EuclideanJordanAlgebra J]` in context,
`example (S : NonUnitalSubalgebra ℝ J) : IsCommJordan ↥S := inferInstance` fails to synthesise,
while the same `example` for `NonUnitalNonAssocCommRing ↥S` succeeds.  The conclusion drawn from
it still does not apply, because under `EuclideanJordan/Class.lean`'s design **no transfer is
    needed**.
The class puts `Mul` and `One` on top of an inner-product space rather than alongside a ring
structure, so the natural subobject is the same shape one level down: the ambient
`Submodule ℝ J`, whose subtype already carries
`NormedAddCommGroup`, `InnerProductSpace ℝ` and `Module ℝ` from Mathlib, with `Mul` and `One`
added on top.  Then `EuclideanJordanAlgebra ↥(peirceOneSub hc)` is *constructed* from six
field proofs, every one of which is the ambient identity read through `Subtype.ext`, and
`IsCommJordan`, `IsScalarTower`, `SMulCommClass` and the ring structure then arrive on the
subtype the same way they arrive on `J`: as `EuclideanJordan/Class.lean`'s derived instances.
    Nothing is
transferred because nothing has to be.

★ **One rough edge, measured rather than predicted.**  `IsFormallyReal ↥(peirceOneSub hc)` does
*not* come back from a bare `inferInstance`, though `IsCommJordan ↥(peirceOneSub hc)`,
`IsScalarTower`, `SMulCommClass` and `NonUnitalNonAssocCommRing` all do.  The cause is
`IsFormallyReal`'s keying: it is indexed on `[Mul J]` **and** `[AddCommMonoid J]` as two
independent arguments, and on a `Submodule` subtype a bare goal picks
`(peirceOneSub hc).addCommMonoid` while `EuclideanJordan/Class.lean`'s instance carries the
ring-derived `AddCommMonoid`.  The two are **definitionally equal** — both `rfl`-checked, as are
the two `Mul` paths — so this is an elaboration-order artifact and not a diamond, and it costs
nothing where it matters: every consumer in the tree demands `IsFormallyReal` downstream of a
`NonUnitalNonAssocCommRing` argument, so the ring-derived path is the one in the goal and the
instance matches.  `spectral_resolution_complete'` therefore runs inside `J₂(c)` unaided.
Should a bare goal ever be wanted, `EuclideanJordanAlgebra.instIsFormallyReal
(J := ↥(peirceOneSub hc))` supplies it — pinning the type is what fixes it, since without it the
instance arguments are synthesised against a metavariable.  No such instance is declared here,
because nothing needs one.

Three facts make this work.  None is asserted here on the strength of a past probe: each is
re-checked every time the file compiles, at the declaration named after it.

* `NormedAddCommGroup ↥W` and `InnerProductSpace ℝ ↥W` synthesise for any `W : Submodule ℝ J` —
  without which `instEJAPeirceOneSub` could not even be stated, since the class is indexed by
  them;
* the inner product on the subtype is the ambient one **by `rfl`**, which is why
  `instEJAPeirceOneSub`'s `inner_assoc` field is the ambient `inner_assoc` applied to the
  coercions with no rewriting at all;
* membership in the two carriers is *definitionally* the eigenvalue equation, which is why
  `instMulPeirceOneSub` passes `eigen_one_mul_one hc x.2 y.2` straight in as the closure proof
  and `instEJAPeirceOneSub`'s `one_mul` field is `Subtype.ext x.2`.

The plan's *specific* warning — that the class carries `One`, so the instance on `J₂(q)` is
constructed with `1 = q` rather than derived, and `simp`-normal-form care is owed around
`(1 : ↥S)` — is exactly right and is paid here by `coe_one_peirceOneSub` and
`coe_one_peirceZeroSub`, two `@[simp]` lemmas pinning `((1 : ↥(peirceOneSub hc)) : J) = c` and
`((1 : ↥(peirceZeroSub hc)) : J) = 1 - c`.

The `NonUnitalSubalgebra` versions are **not** built.  Nothing downstream needs the subalgebra
lattice, and `Submodule.finrank_lt` — which the dimension-drop lemmas below consume — wants a
`Submodule` anyway.

## Naming: eigenvalues, not Jacobson indices

The literature writes the eigenvalue-`1` and eigenvalue-`0` Peirce spaces as `J₂(c)` and
`J₀(c)`, indexing by twice the eigenvalue.  The tree's existing projections are named by the
eigenvalue itself (`peirceOne`, `peirceHalf`, `peirceZero`), and consistency inside the tree
wins: `peirceOneSub hc` **is** `J₂(c)` and `peirceZeroSub hc` **is** `J₀(c)`.  Reading
`peirceOneSub` as `J₁(c)` — the half-eigenspace — would be a mistake.  The half-eigenspace gets
no subalgebra here, and cannot get one on the same terms: `EuclideanJordan/PeirceMul.lean`'s
`peirceHalf_mul_half_eq_zero` puts the product of two half-eigenvectors in `J₂(c) ⊕ J₀(c)`, so
the half-eigenspace is closed under the product only in the degenerate case where it squares to
zero.

## Scope

-/

@[expose] public section

noncomputable section

namespace EuclideanJordan

open EuclideanJordanAlgebra (smul_mul jordan inner_assoc mul_one')

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [EuclideanJordanAlgebra J]

/-! ## The two carriers -/

/-- **`J₂(c)`**, the eigenvalue-`1` Peirce space `{x | c ∘ x = x}`, as a submodule.

The idempotency hypothesis is carried but unused: the eigenspace of any element is a submodule.
It is present so that the *type* `↥(peirceOneSub hc)` records it, which is what lets the
`Mul`, `One` and `EuclideanJordanAlgebra` instances below be found by synthesis. -/
def peirceOneSub {c : J} (_hc : c * c = c) : Submodule ℝ J where
  carrier := {x : J | c * x = x}
  add_mem' := fun {a b} ha hb => by
    change c * (a + b) = a + b
    rw [mul_add, ha, hb]
  zero_mem' := mul_zero c
  smul_mem' := fun r x hx => by
    change c * (r • x) = r • x
    rw [mul_smul_comm, hx]

@[simp] theorem mem_peirceOneSub {c : J} (hc : c * c = c) {x : J} :
    x ∈ peirceOneSub hc ↔ c * x = x := Iff.rfl

/-- **`J₀(c)`**, the eigenvalue-`0` Peirce space `{x | c ∘ x = 0}`, as a submodule. -/
def peirceZeroSub {c : J} (_hc : c * c = c) : Submodule ℝ J where
  carrier := {x : J | c * x = 0}
  add_mem' := fun {a b} ha hb => by
    change c * (a + b) = 0
    rw [mul_add, ha, hb, add_zero]
  zero_mem' := mul_zero c
  smul_mem' := fun r x hx => by
    change c * (r • x) = 0
    rw [mul_smul_comm, hx, smul_zero]

@[simp] theorem mem_peirceZeroSub {c : J} (hc : c * c = c) {x : J} :
    x ∈ peirceZeroSub hc ↔ c * x = 0 := Iff.rfl

/-! ## `J₂(c)` is a Euclidean Jordan algebra with unit `c` -/

section Two

variable {c : J} (hc : c * c = c)

/-- Closure under the product is `EuclideanJordan/PeirceMul.lean`'s `eigen_one_mul_one`, applied
to the
membership proofs directly: membership unfolds to the eigenvalue equation. -/
instance instMulPeirceOneSub : Mul ↥(peirceOneSub hc) :=
  ⟨fun x y => ⟨(x : J) * (y : J), eigen_one_mul_one hc x.2 y.2⟩⟩

/-- ★ **The unit of `J₂(c)` is `c`, not `1`.** -/
instance instOnePeirceOneSub : One ↥(peirceOneSub hc) := ⟨⟨c, hc⟩⟩

@[simp] theorem coe_mul_peirceOneSub (x y : ↥(peirceOneSub hc)) :
    ((x * y : ↥(peirceOneSub hc)) : J) = (x : J) * (y : J) := rfl

@[simp] theorem coe_one_peirceOneSub : ((1 : ↥(peirceOneSub hc)) : J) = c := rfl

/-- **`J₂(c)` is a Euclidean Jordan algebra.**  Every field is the ambient identity at the
coercions; `one_mul` is the membership proof itself. -/
instance instEJAPeirceOneSub : EuclideanJordanAlgebra ↥(peirceOneSub hc) :=
  { (inferInstance : Mul ↥(peirceOneSub hc)), (inferInstance : One ↥(peirceOneSub hc)) with
    mul_comm := fun x y => Subtype.ext (_root_.mul_comm (x : J) (y : J))
    add_mul := fun x y z => Subtype.ext (_root_.add_mul (x : J) (y : J) (z : J))
    smul_mul := fun r x y => Subtype.ext (smul_mul r (x : J) (y : J))
    one_mul := fun x => Subtype.ext x.2
    jordan := fun x y => Subtype.ext (jordan (x : J) (y : J))
    inner_assoc := fun x y z => inner_assoc (x : J) (y : J) (z : J) }

end Two

/-! ## `J₀(c)` is a Euclidean Jordan algebra with unit `1 - c` -/

section Zero

variable {c : J} (hc : c * c = c)

theorem one_sub_mem_peirceZeroSub : (1 : J) - c ∈ peirceZeroSub hc := by
  change c * (1 - c) = 0
  rw [mul_sub, mul_one', hc, sub_self]

instance instMulPeirceZeroSub : Mul ↥(peirceZeroSub hc) :=
  ⟨fun x y => ⟨(x : J) * (y : J), eigen_zero_mul_zero hc x.2 y.2⟩⟩

/-- ★ **The unit of `J₀(c)` is `1 - c`.** -/
instance instOnePeirceZeroSub : One ↥(peirceZeroSub hc) :=
  ⟨⟨(1 : J) - c, one_sub_mem_peirceZeroSub hc⟩⟩

@[simp] theorem coe_mul_peirceZeroSub (x y : ↥(peirceZeroSub hc)) :
    ((x * y : ↥(peirceZeroSub hc)) : J) = (x : J) * (y : J) := rfl

@[simp] theorem coe_one_peirceZeroSub : ((1 : ↥(peirceZeroSub hc)) : J) = 1 - c := rfl

/-- **`J₀(c)` is a Euclidean Jordan algebra.** -/
instance instEJAPeirceZeroSub : EuclideanJordanAlgebra ↥(peirceZeroSub hc) :=
  { (inferInstance : Mul ↥(peirceZeroSub hc)), (inferInstance : One ↥(peirceZeroSub hc)) with
    mul_comm := fun x y => Subtype.ext (_root_.mul_comm (x : J) (y : J))
    add_mul := fun x y z => Subtype.ext (_root_.add_mul (x : J) (y : J) (z : J))
    smul_mul := fun r x y => Subtype.ext (smul_mul r (x : J) (y : J))
    one_mul := fun x => Subtype.ext (by
      change ((1 : J) - c) * (x : J) = (x : J)
      rw [sub_mul, EuclideanJordanAlgebra.one_mul, x.2, sub_zero])
    jordan := fun x y => Subtype.ext (jordan (x : J) (y : J))
    inner_assoc := fun x y z => inner_assoc (x : J) (y : J) (z : J) }

end Zero

/-! ## The dimension drop

The two lemmas that make an induction on `finrank ℝ J` down the Peirce decomposition
terminate.  Each is a one-element argument: if the subalgebra were everything it would contain
the ambient unit (resp. `c` itself), and its defining equation would then force `c = 1`
(resp. `c = 0`). -/

section Finrank

variable [FiniteDimensional ℝ J] {c : J} (hc : c * c = c)

theorem finrank_peirceOneSub_lt (hne : c ≠ 1) :
    Module.finrank ℝ ↥(peirceOneSub hc) < Module.finrank ℝ J := by
  refine Submodule.finrank_lt ?_
  intro htop
  have h1 : (1 : J) ∈ peirceOneSub hc := by rw [htop]; exact Submodule.mem_top
  have h2 : c * (1 : J) = 1 := h1
  exact hne (by rwa [mul_one'] at h2)

theorem finrank_peirceZeroSub_lt (hne : c ≠ 0) :
    Module.finrank ℝ ↥(peirceZeroSub hc) < Module.finrank ℝ J := by
  refine Submodule.finrank_lt ?_
  intro htop
  have h1 : c ∈ peirceZeroSub hc := by rw [htop]; exact Submodule.mem_top
  have h2 : c * c = 0 := h1
  exact hne (by rwa [hc] at h2)

end Finrank

end EuclideanJordan
