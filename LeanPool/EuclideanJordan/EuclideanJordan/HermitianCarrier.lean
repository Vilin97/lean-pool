/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.EuclideanJordan.EuclideanJordan.FramePeirce
public import LeanPool.EuclideanJordan.EuclideanJordan.Witness
public import LeanPool.EuclideanJordan.EuclideanJordan.HermitianBilin



/-!
# A carrier for `EuclideanJordanAlgebra`

`EuclideanJordan/Class.lean` names the Euclidean Jordan algebra hypothesis as a class, and
    `EuclideanJordan/Rank.lean`,
`EuclideanJordan/FrameExists.lean` and `EuclideanJordan/FramePeirce.lean` state their results
    over it.  Until this file
the **only** instances of that class in the tree were `EuclideanJordan/PeirceSubalgebra.lean`'s
    two, and both
are conditional on an ambient `[EuclideanJordanAlgebra J]`, so nothing exhibited a base model:
`exists_jordanFrame` and `frameBlock_isInternal` were universally quantified over a class no
object was known to inhabit.

This file supplies the base model.  `H_n(𝕜)` — Hermitian matrices over an `RCLike` field, under
the symmetrized product `A ∘ B = ½(AB + BA)` and the real trace form — is a
`EuclideanJordanAlgebra`.

★ **This is the same exposure the layer has had to close for every other hypothesis it carries.**
An abstract theorem whose hypothesis no carrier is known to satisfy is worth nothing;
`EuclideanJordan/Witness.lean`'s `instIsFormallyReal` and `diagFrame_orthIdem` close it for
`IsFormallyReal` and `IsOrthIdemFamily`, and this file closes it for `EuclideanJordanAlgebra`.

★ The class was **not** the only unwitnessed hypothesis left in the layer, and an earlier draft
of this docstring said it was.  `EuclideanJordan/Rank.lean`'s `IsPrimitive` and `JordanFrame`
    had no witness
either — `EuclideanJordan/Witness.lean` builds the diagonal matrix units but never proves one
    primitive, so
no `JordanFrame` had ever been constructed.  Both are witnessed at the end of this file, but by a
separate argument, and the class instance alone would not have supplied them.

## No field needed new mathematics

Every one of the class's six field obligations was already proved in the tree, in
`jordanBilinG` or `symmMul` vocabulary:

| class field | discharged by |
| --- | --- |
| `mul_comm` | `HermitianMat.symmMul_comm` |
| `add_mul` | bilinearity of `EuclideanJordan/HermitianBilin.lean`'s `jordanBilinG` |
| `smul_mul` | bilinearity of `EuclideanJordan/HermitianBilin.lean`'s `jordanBilinG` |
| `one_mul` | `HermitianMat.one_symmMul` |
| `jordan` | `EuclideanJordan/Order.lean`'s `hermitian_jordan_id` (the vendored `IsCommJordan`) |
| `inner_assoc` | `EuclideanJordan/Order.lean`'s `hermitian_jordan_assoc` |

The three lemmas before the instance are re-orientations, not new results: two unbundle
`jordanBilinG`'s `LinearMap` structure, and `hermitian_symmMul_jordan` turns Mathlib's
`lmul_comm_rmul_rmul` orientation into the class's by commuting the product twice.

## The diamond `EuclideanJordan/Class.lean` warned about, measured

`EuclideanJordan/Class.lean` records that `instNonUnitalNonAssocCommRing` fires on any type
    carrying the
class, that `HermitianMat d 𝕜` already carries a `Mul` from
`EuclideanJordan/Vendor/HermitianMat/Jordan.lean`'s `scoped instance : CommMagma`, and that
"if one is ever declared, that scoped instance and this class's `toMul` will both be in scope
inside `open HermMul` sections and one of them has to give way."

That is now declared, and the collision is **definitional**: `hermMul_toMul_eq` below is `rfl`.
Both `Mul` structures have `HermitianMat.symmMul` as their multiplication, so which one instance
search returns does not change any statement.  Concretely, inside an `open HermMul` section with
this instance in scope, `#synth Mul (HermitianMat (Fin 2) ℂ)` returns *this* instance's `toMul`
(the global instance outranks the opened scoped one), `HermMul.mul_eq_symmMul` still typechecks,
and `EuclideanJordan/Order.lean`'s two `open HermMul` proofs — `hermitian_jordan_id` and
`hermitian_formallyReal` — still go through unaltered.

★ Two things this does *not* claim.  It is not claimed that the collision is invisible: instance
search does return a different term inside `open HermMul` once this module is imported, and a
proof that pins the instance by name rather than by its product would notice.  And it is not
claimed that anything currently pays that cost.  ★ Every `open HermMul` site in this library —
`EuclideanJordan/Order.lean`, `EuclideanJordan/Spectral.lean` and `EuclideanJordan/Witness.lean` —
is strictly *upstream* of this file: this file's import closure contains all three, and imports
are directional, so none of them can see this instance.  ★ A **downstream** module that both
imports this file and opens `HermMul` is a different matter: it would see the collision, and would
have to navigate it rather than avoid it, bridging with `hermitian_mul_eq_symmMul`.  That does not
change what the three sites above see.

★ One elaboration trap, recorded because it cost a probe round.  Inside the structure-instance
notation, `simpa only [...] using e` **fails** on fields whose statement is in `*` form while `e`
is in `symmMul` form, reporting a type mismatch between `(A + B) * C` and `(A + B).symmMul C`
even though the two are `rfl`-equal (`hermitian_mul_eq_symmMul` below).  The named-lemma route
(`add_mul A B C := hermitian_symmMul_add_left A B C`) succeeds on the same goal.  So the
mismatch is `simpa`'s reducibility setting, not a real failure of the defeq — do not conclude
from such a message that the product is wrong.

## Scope

This file is substrate: it proves no new theorem about Jordan algebras.  What changes is that the
M3/M4 results are now known to be about a nonempty class: `hermitian_exists_jordanFrame` and
`hermitian_frameBlock_isInternal` are `exists_jordanFrame` and `frameBlock_isInternal` read on
`H_n(𝕜)`.

★ The last section goes past existence and **names a frame** on `H_n(ℂ)`: `diagJordanFrame`, the
diagonal matrix units of `EuclideanJordan/Witness.lean` reindexed along `Fintype.equivFin`.
    Unlike the class
instance, that is not repackaging: `diagFrame_isPrimitive` is the one obligation of `JordanFrame`
that no lemma in the tree discharges — `diagFrame_orthIdem` gives `orthIdem` and `diagFrame_sum`
gives `complete`, and `p` is data — and its proof and the four entrywise lemmas under it are
written here.  (`hermitian_one_ne_zero` is new too, but it is three lines and reads off one
matrix entry.)  ★ Note what primitivity is **not**: it is not
`dim V_ii = 1`, and this file does not prove that.  Two scope limits on the frame: it is over
`ℂ` only, because `EuclideanJordan/Witness.lean`'s `diagFrame` is, and its cardinality is
    `Fintype.card n`,
which is **not** proved to be the rank — `EuclideanJordan/Rank.lean` proves only `card ≤ rank` and
`card ≤ finrank`.
-/

@[expose] public section

noncomputable section

namespace EuclideanJordan

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]

/-! ## The three re-orientations the class fields need -/

/-- Additivity of `∘` in its left argument, from `jordanBilinG`'s `LinearMap` structure. -/
theorem hermitian_symmMul_add_left (A B C : HermitianMat n 𝕜) :
    (A + B).symmMul C = A.symmMul C + B.symmMul C := by
  simpa only [jordanBilin_applyG] using (jordanBilinG (n := n) 𝕜).map_add₂ A B C

omit [DecidableEq n] in
/-- Real homogeneity of `∘` in its left argument, from `jordanBilinG`'s `LinearMap` structure. -/
theorem hermitian_symmMul_smul_left (r : ℝ) (A B : HermitianMat n 𝕜) :
    (r • A).symmMul B = r • (A.symmMul B) := by
  classical
  simpa only [jordanBilin_applyG] using (jordanBilinG (n := n) 𝕜).map_smul₂ r A B

omit [DecidableEq n] in
/-- The Jordan identity in the class's orientation, `x ∘ (x² ∘ y) = x² ∘ (x ∘ y)`.
`EuclideanJordan/Order.lean`'s `hermitian_jordan_id` carries Mathlib's orientation
`(x ∘ y) ∘ x² = x ∘ (y ∘ x²)`; the two differ by commuting the product twice. -/
theorem hermitian_symmMul_jordan (A B : HermitianMat n 𝕜) :
    A.symmMul ((A.symmMul A).symmMul B) = (A.symmMul A).symmMul (A.symmMul B) := by
  classical
  have h := hermitian_jordan_id (n := n) (𝕜 := 𝕜) A B
  simp only [jordanBilin_applyG] at h
  rw [HermitianMat.symmMul_comm (A.symmMul A) B, ← h]
  exact HermitianMat.symmMul_comm _ _

/-! ## The instance -/

/-- ★★★ **`H_n(𝕜)` is a Euclidean Jordan algebra.**  The class of `EuclideanJordan/Class.lean`,
on the
Hermitian-matrix carrier, at the generality `EuclideanJordan/Order.lean` uses: any `RCLike` scalar
field and any finite decidable index type. -/
instance instEuclideanJordanAlgebraHermitianMat :
    EuclideanJordanAlgebra (HermitianMat n 𝕜) where
  mul := HermitianMat.symmMul
  one := 1
  mul_comm A B := HermitianMat.symmMul_comm A B
  add_mul A B C := hermitian_symmMul_add_left A B C
  smul_mul r A B := hermitian_symmMul_smul_left r A B
  one_mul A := HermitianMat.one_symmMul A
  jordan A B := hermitian_symmMul_jordan A B
  inner_assoc A B C := hermitian_jordan_assoc A B C

/-! ### Fidelity: the class's product is the intended one

Inhabitedness alone would be satisfied by any product making the fields true.  These three
`rfl`s pin the instance's `*` to the three names the rest of the tree uses for `A ∘ B`. -/

/-- The class's product on `H_n(𝕜)` is `HermitianMat.symmMul`. -/
theorem hermitian_mul_eq_symmMul (A B : HermitianMat n 𝕜) : A * B = A.symmMul B := rfl

/-- The class's product on `H_n(𝕜)` is `jordanBilinG`, the bundled bilinear form of the same
product. -/
theorem hermitian_mul_eq_jordanBilinG (A B : HermitianMat n 𝕜) :
    A * B = jordanBilinG 𝕜 A B := rfl

/-- ★ **The `HermMul` collision is definitional.**  The `Mul` this instance supplies and the one
`EuclideanJordan/Vendor/HermitianMat/Jordan.lean`'s scoped `CommMagma` supplies are the same
structure, so which one instance search returns inside an `open HermMul` section cannot change a
statement.  See the module docstring for what this does and does not claim. -/
theorem hermMul_toMul_eq :
    (HermMul.instCommMagmaHermitianMat (d := n) (𝕜 := 𝕜)).toMul
      = (instEuclideanJordanAlgebraHermitianMat (n := n) (𝕜 := 𝕜)).toMul := rfl

/-! ## Nontriviality -/

/-- `1 ≠ 0` in `H_n(𝕜)` whenever the index type is nonempty: read off the `(i, i)` entry. -/
theorem hermitian_one_ne_zero [Nonempty n] : (1 : HermitianMat n 𝕜) ≠ 0 := by
  intro h
  have h2 := congrArg
    (fun A : HermitianMat n 𝕜 => A.mat (Classical.arbitrary n) (Classical.arbitrary n)) h
  simp only [HermitianMat.mat_one, HermitianMat.mat_zero, Matrix.one_apply_eq,
    Matrix.zero_apply] at h2
  exact one_ne_zero h2

omit [Fintype n] [DecidableEq n] in
instance instNontrivialHermitianMat [Finite n] [Nonempty n] :
    Nontrivial (HermitianMat n 𝕜) := by
  let : DecidableEq n := Classical.decEq n
  let := Fintype.ofFinite n
  exact ⟨⟨1, 0, hermitian_one_ne_zero⟩⟩

/-! ## M3 and M4 on the carrier

The two results now read on a live object rather than on a class with no known inhabitant.
Neither proof is new: each is the abstract theorem with `J := H_n(𝕜)`. -/

/-- **(M3) on `H_n(𝕜)`.**  `EuclideanJordan/FrameExists.lean`'s `exists_jordanFrame`,
instantiated.  The
finite-dimensionality it needs is `HermitianMat.FiniteDimensional`; the nontriviality is
`hermitian_one_ne_zero`. -/
theorem hermitian_exists_jordanFrame [Nonempty n] :
    ∃ k, Nonempty (JordanFrame (HermitianMat n 𝕜) k) :=
  exists_jordanFrame (HermitianMat n 𝕜) hermitian_one_ne_zero

/-- **(M4) on `H_n(𝕜)`.**  `EuclideanJordan/FramePeirce.lean`'s `frameBlock_isInternal`,
instantiated: a
Jordan frame of `H_n(𝕜)` splits it as the internal direct sum of its diagonal and coherence
blocks. -/
theorem hermitian_frameBlock_isInternal {k : ℕ} (F : JordanFrame (HermitianMat n 𝕜) k) :
    DirectSum.IsInternal (frameBlock F) :=
  frameBlock_isInternal F

/-- **(M3) and (M4) together on `H_n(𝕜)`**: the algebra has a Jordan frame, and that frame
decomposes it.  This is the statement that was universally quantified over an unwitnessed class
before this file. -/
theorem hermitian_exists_frame_isInternal [Nonempty n] :
    ∃ (k : ℕ) (F : JordanFrame (HermitianMat n 𝕜) k), DirectSum.IsInternal (frameBlock F) := by
  obtain ⟨k, ⟨F⟩⟩ := hermitian_exists_jordanFrame (n := n) (𝕜 := 𝕜)
  exact ⟨k, F, frameBlock_isInternal F⟩

/-! ## A named frame on `H_n(ℂ)`

`EuclideanJordan/Witness.lean` builds the diagonal matrix units `E_ii` and proves them orthogonal
idempotents summing to the unit.  That is three of `JordanFrame`'s four fields.  The missing one
is **primitivity**, which is proved here.

The argument is entrywise and short.  If `d` is fixed by `E_ii ∘ -` then reading the `(a, b)`
entry of `½(E_ii D + D E_ii) = D` gives `D_ab = 0` off `(i, i)` — the three off-diagonal cases
reduce to `½ D_ab = D_ab` or to `0 = D_ab` — so `D = D_ii · E_ii`.  Idempotency then forces
`D_ii² = D_ii` at the surviving entry, so `D_ii ∈ {0, 1}` and `d` is `0` or `E_ii`. -/

section Frame

open Witness

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
/-- The diagonal matrix unit entrywise: `1` at `(i, i)` and `0` elsewhere. -/
theorem diagFrame_mat_apply (i a b : n) :
    (diagFrame i).mat a b = if a = b then (if a = i then (1 : ℂ) else 0) else 0 := by
  rw [diagFrame_mat, Matrix.diagonal_apply]
  split_ifs <;> simp_all

/-- The entries of `E_ii ∘ D`.  Left multiplication by `E_ii` keeps row `i`, right
multiplication keeps column `i`, so the symmetrized product halves everything meeting the cross
at `i` exactly once and kills everything off it. -/
theorem diagFrame_symmMul_mat_apply (i : n) (D : HermitianMat n ℂ) (a b : n) :
    ((diagFrame i).symmMul D).mat a b
      = (2 : ℂ)⁻¹ * ((if a = i then D.mat a b else 0) + (if b = i then D.mat a b else 0)) := by
  rw [HermitianMat.symmMul_toMat]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, smul_eq_mul]
  congr 1
  congr 1
  · rw [Finset.sum_eq_single a]
    · rw [diagFrame_mat_apply]; simp
    · intro k _ hk; rw [diagFrame_mat_apply]; simp [Ne.symm hk]
    · intro h; exact absurd (Finset.mem_univ a) h
  · rw [Finset.sum_eq_single b]
    · rw [diagFrame_mat_apply]; simp [eq_comm]
    · intro k _ hk; rw [diagFrame_mat_apply]; simp [hk]
    · intro h; exact absurd (Finset.mem_univ b) h

/-- **An element fixed by `E_ii ∘ -` lives at the single entry `(i, i)`.**  Note this uses only
the fixed-point hypothesis, not idempotency of `D`. -/
theorem mat_eq_zero_of_diagFrame_fixed {i : n} {D : HermitianMat n ℂ}
    (h : (diagFrame i).symmMul D = D) {a b : n} (hab : ¬(a = i ∧ b = i)) :
    D.mat a b = 0 := by
  have he := congrArg (fun M : HermitianMat n ℂ => M.mat a b) h
  simp only [diagFrame_symmMul_mat_apply] at he
  by_cases ha : a = i <;> by_cases hb : b = i
  · exact absurd ⟨ha, hb⟩ hab
  · rw [ite_eq_left ha, ite_eq_right hb, add_zero] at he
    linear_combination -2 * he
  · rw [ite_eq_right ha, ite_eq_left hb, zero_add] at he
    linear_combination -2 * he
  · rw [ite_eq_right ha, ite_eq_right hb, add_zero, mul_zero] at he
    exact he.symm

/-- So such an element is a scalar multiple of `E_ii`. -/
theorem mat_eq_smul_of_diagFrame_fixed {i : n} {D : HermitianMat n ℂ}
    (h : (diagFrame i).symmMul D = D) :
    D.mat = D.mat i i • (diagFrame i).mat := by
  ext a b
  rw [Matrix.smul_apply, diagFrame_mat_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = i
    · subst ha; simp
    · rw [mat_eq_zero_of_diagFrame_fixed h (fun hc => ha hc.1)]; simp [ha]
  · rw [mat_eq_zero_of_diagFrame_fixed h (fun hc => hab (hc.1.trans hc.2.symm))]; simp [hab]

/-- ★★ **The diagonal matrix units are primitive.**  The one obligation of `JordanFrame` that
`EuclideanJordan/Witness.lean` leaves open, and the only new mathematics in this file. -/
theorem diagFrame_isPrimitive (i : n) : IsPrimitive (diagFrame (d := n) i) := by
  refine ⟨(diagFrame_orthIdem (d := n)).idem i, ?_, ?_⟩
  · intro h
    have hii := congrArg (fun M : HermitianMat n ℂ => M.mat i i) h
    rw [diagFrame_mat_apply] at hii
    simp at hii
  · intro D hD hcD
    have hsupp : D.mat = D.mat i i • (diagFrame i).mat := mat_eq_smul_of_diagFrame_fixed hcD
    -- the Jordan square of `D` is its matrix square, since `D` commutes with itself
    have hD' : D.symmMul D = D := hD
    have hsq : D.mat * D.mat = D.mat := by
      have hm := congrArg HermitianMat.mat hD'
      rwa [HermitianMat.symmMul_self] at hm
    have hii : D.mat i i * D.mat i i = D.mat i i := by
      have hentry := congrFun (congrFun hsq i) i
      rw [Matrix.mul_apply, Finset.sum_eq_single i] at hentry
      · exact hentry
      · intro k _ hk
        rw [mat_eq_zero_of_diagFrame_fixed hcD (fun hc => hk hc.2), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
    have hfac : D.mat i i * (D.mat i i - 1) = 0 := by linear_combination hii
    rcases mul_eq_zero.mp hfac with h0 | h1
    · left
      apply HermitianMat.ext
      rw [hsupp, h0, zero_smul, HermitianMat.mat_zero]
    · right
      apply HermitianMat.ext
      rw [hsupp, sub_eq_zero.mp h1, one_smul]

/-- ★★★ **A Jordan frame on `H_n(ℂ)`, named.**  The diagonal matrix units, reindexed along
`Fintype.equivFin` because `JordanFrame` is `Fin`-indexed.  ★ Its cardinality `Fintype.card n`
is **not** claimed to be the rank of the algebra — `EuclideanJordan/Rank.lean` proves only that
    a frame's
cardinality is bounded by the rank and by the dimension. -/
noncomputable def diagJordanFrame : JordanFrame (HermitianMat n ℂ) (Fintype.card n) where
  p k := diagFrame ((Fintype.equivFin n).symm k)
  orthIdem :=
    ⟨fun _ => (diagFrame_orthIdem (d := n)).idem _,
     fun _ _ hkl => (diagFrame_orthIdem (d := n)).orth _ _
       ((Fintype.equivFin n).symm.injective.ne hkl)⟩
  primitive _ := diagFrame_isPrimitive _
  complete := by
    rw [Equiv.sum_comp (Fintype.equivFin n).symm diagFrame]
    exact diagFrame_sum

@[simp] theorem diagJordanFrame_p (k : Fin (Fintype.card n)) :
    (diagJordanFrame (n := n)).p k = diagFrame ((Fintype.equivFin n).symm k) := rfl

/-- **(M4) on a named frame.**  `H_n(ℂ)` is the internal direct sum of the Peirce blocks of the
diagonal frame — the frame Peirce decomposition with nothing left quantified. -/
theorem diagJordanFrame_isInternal :
    DirectSum.IsInternal (frameBlock (diagJordanFrame (n := n))) :=
  frameBlock_isInternal _

end Frame

end EuclideanJordan
