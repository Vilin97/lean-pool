/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Pauli strings: the binary symplectic representation, with phase

The paper describes an `n`-qubit Pauli operator as an element of `{I,X,Y,Z}^{⊗n}` and, in
`def:pauli_basis`, takes the `2^{-n/2}`-normalized version of that set as an orthonormal basis of
operators. This file supplies a combinatorial representation of such operators — pairs of bit
vectors with an explicit phase — on which the group law, the adjoint and the commutation relation
are computable, and proves that any two Pauli strings either commute or anticommute.

**What is defined here is the phase-extended Pauli group, not the basis of `def:pauli_basis`.**
`PauliString n` has `4 · 4^n` elements, four phase variants of each of the `4^n` signless strings,
and those variants are scalar multiples of one another: `toMatrix (phaseMul 1 s) = i · toMatrix s`.
So the image of `toMatrix` is *not* linearly independent, and `toMatrix_injective` — which is
about the group — must not be read as saying it is. Cutting the group down to a canonical `4^n`
basis needs a phase normalization (`phase = #{Y-sites} mod 4`, so that the operator is the
positive tensor product) and the `2^{-n/2}` normalization. `Pauli/Tensor.lean` supplies the
representatives with that phase and their exact Kronecker-product interpretation;
`Pauli/Trace.lean` proves the unnormalized trace pairing, and `Pauli/Coeff.lean` uses the
normalized Pauli 2-norm.

## The representation

A Pauli string is a pair of bit vectors together with a phase,

  `s = i^{phase} · X^{x} Z^{z}`,   `x z : Fin n → ZMod 2`,   `phase : ZMod 4`.

This is the binary symplectic representation with the phase carried explicitly — the same design
as `inQWIRE/LeanQuantum`'s `Pauli n = {m : ZMod 4, z x : BitVec n}`, up to which of `X` and `Z`
sits on the left. `Stavan-Jain/QECLean` makes a different choice for its Pauli group: an inductive
`{I,X,Y,Z}`-valued function with a `Fin 4` phase, from which it derives a separate, phase-forgetting
symplectic vector for check matrices.

The phase is **not** optional bookkeeping: `X * Z = -i · (i X Z) = -i Y`,
so the product of two elements of `{I,X,Y,Z}^{⊗n}` is only in that set up to a fourth root of
unity, and a phaseless representation is a group only modulo phase. Carrying `ZMod 4` makes the
product law exact, which is what lets `Pauli/Matrix.lean` build a representation that is a
monoid homomorphism on the nose rather than projectively.

## Main definitions

* `PauliString n`: the structure `⟨x, z, phase⟩`, read as `i^{phase} X^x Z^z`.
* `sympForm s t = s.x ⬝ᵥ t.z + s.z ⬝ᵥ t.x : ZMod 2`: the symplectic form.
* `phaseMul k s`: the string `i^k · s`.
* `X1`, `Z1`, `Y1`: the one-qubit Pauli strings, used as witnesses.

## Main results

* `PauliString n` is a `Group` (the `n`-qubit Pauli group) under
  `(s * t).phase = s.phase + t.phase + signPhase (s.z ⬝ᵥ t.x)`.
* `sympForm` measures the failure to commute, exactly: `mul_eq_phaseMul_sympForm` says
  `s * t = i^{2⟪s,t⟫} · (t * s)` — one identity from which both branches follow
  (`commute_iff_sympForm_eq_zero`, `anticommute_iff_sympForm_eq_one`).
* **`commute_or_anticommute`**: any two Pauli strings either commute or anticommute. This is
  what makes the two cases `[G,P] = 0` and `{G,P} = 0` of `apd:eq:pauli_rotation_branch`
  exhaustive. `Lean4LPD.rot_conj_of_commute` and `Lean4LPD.rot_conj_of_anticommute` cover the two
  branches over an abstract algebra, where nothing rules out a third. It is a short consequence
  of `sympForm` landing in `ZMod 2`, but the point is that the case split has to be *routed
  through* a two-valued invariant to be exhaustive at all.
  (`QECLean` proves the same statement for its own representation; see the `Group` instance.)
* `isSelfAdjoint_iff_mul_self_eq_one`: `IsSelfAdjoint s ↔ s * s = 1`, so for a Pauli string
  Hermiticity and squaring to one coincide. `Rotation.lean` needs both — `hG : G * G = 1` and
  `star G = G` — and for a general operator the first does not follow from the second. For Pauli
  strings it does, because they are unitary (`star_eq_inv`).
* `isSelfAdjoint_phaseMul_one_mul` and `sympForm_mul_self_right`: for Hermitian anticommuting
  `G` and `s`, the partner `i G s` is again Hermitian and again anticommutes with `G`.

`Pauli/Weight.lean` adds the weight; `Pauli/Matrix.lean` adds the matrix model and transports the
dichotomy to operators, where `Rotation.lean` can consume it.

## Conventions

The phase convention `i^{phase} X^x Z^z` with product phase `p_s + p_t + 2⟪z_s, x_t⟫` is the
standard one; it is forced by `Z^{z_s} X^{x_t} = (-1)^{z_s · x_t} X^{x_t} Z^{z_s}`, which is what
has to be paid to push the `X`-parts of a product to the left. Hermiticity is then
`phase ≡ z ⬝ᵥ x (mod 2)` (`isSelfAdjoint_iff_phase`). Note what that does and does not fix: it
pins the phase's *parity*, and the two admissible phases differ by `2`, giving `A` and `−A`. Both
are self-adjoint, so this criterion does not select a canonical sign — at one qubit it admits
both `Y` and `−Y`. The canonical signless representative needs `phase = #{Y-sites} mod 4`, which
is a finer condition than the parity one and is not used here.
-/

namespace Lean4LPD

/-! ### The sign-to-phase embedding

`(-1)^a = i^{2a}`, so a sign bit enters the phase group doubled. Every lemma here is a finite
check over `ZMod 2`, discharged by `decide`. -/

/-- `signPhase a` is the `ZMod 4` phase exponent of the sign `(-1)^a`, defined as `2a`. -/
def signPhase (a : ZMod 2) : ZMod 4 := 2 * (a.val : ZMod 4)

@[simp] lemma signPhase_zero : signPhase 0 = 0 := rfl

@[simp] lemma signPhase_one : signPhase 1 = 2 := rfl

lemma signPhase_add (a b : ZMod 2) : signPhase (a + b) = signPhase a + signPhase b := by
  revert a b; decide

@[simp] lemma signPhase_eq_zero_iff {a : ZMod 2} : signPhase a = 0 ↔ a = 0 := by
  revert a; decide

@[simp] lemma neg_signPhase (a : ZMod 2) : -signPhase a = signPhase a := by revert a; decide

@[simp] lemma signPhase_add_self (a : ZMod 2) : signPhase a + signPhase a = 0 := by
  revert a; decide

lemma signPhase_injective : Function.Injective signPhase := by decide

/-! ### Bit vectors

`Fin n → ZMod 2` is the vector space the `x`- and `z`-parts live in. Only characteristic two is
needed from it. -/

private lemma bit_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

private lemma two_mul_signPhase (a : ZMod 2) : 2 * signPhase a = 0 := by revert a; decide

private lemma bit_add_eq_zero_iff {a b : ZMod 2} : a + b = 0 ↔ a = b := by
  revert a b; decide

/-- Addition of bit vectors is its own inverse. -/
lemma bits_add_self {n : ℕ} (v : Fin n → ZMod 2) : v + v = 0 := by
  funext i; exact bit_add_self (v i)

/-- In characteristic two, `u + v = 0` says `u = v`. -/
lemma bits_add_eq_zero_iff {n : ℕ} {u v : Fin n → ZMod 2} : u + v = 0 ↔ u = v := by
  constructor
  · intro h
    funext i
    exact bit_add_eq_zero_iff.1 (congrFun h i)
  · rintro rfl; exact bits_add_self _

/-! ### Pauli strings -/

/-- An `n`-qubit **Pauli string**, written `i^{phase} · X^{x} Z^{z}`.

This is a *definition* of a representation, not a theorem about one: `Pauli/Matrix.lean` supplies
the operator `toMatrix s` this notation denotes and proves the product law below matches operator
multiplication (`toMatrix_mul`). -/
structure PauliString (n : ℕ) where
  /-- The `X`-part: `x i = 1` where the string carries an `X` or a `Y`. -/
  x : Fin n → ZMod 2
  /-- The `Z`-part: `z i = 1` where the string carries a `Z` or a `Y`. -/
  z : Fin n → ZMod 2
  /-- The phase exponent: the string is `i^{phase} X^{x} Z^{z}`. -/
  phase : ZMod 4

namespace PauliString

variable {n : ℕ} {s t u : PauliString n}

@[ext]
theorem ext' {s t : PauliString n} (hx : s.x = t.x) (hz : s.z = t.z)
    (hp : s.phase = t.phase) : s = t := by
  cases s; cases t; simp_all

/-- Equality is decidable, so concrete Pauli strings can be checked by `decide`. Kept explicit
rather than `deriving`, because the `x` and `z` fields are functions and the derived handler does
not find `Fintype.decidablePiFintype` on its own. -/
instance : DecidableEq (PauliString n) := fun s t =>
  decidable_of_iff (s.x = t.x ∧ s.z = t.z ∧ s.phase = t.phase)
    ⟨fun h => ext' h.1 h.2.1 h.2.2, fun h => by subst h; exact ⟨rfl, rfl, rfl⟩⟩

/-! ### The group law -/

/-- Multiplication: bit vectors add, and the phase picks up `2⟪z_s, x_t⟫` from commuting the
`Z`-part of `s` past the `X`-part of `t`. -/
instance : Mul (PauliString n) where
  mul s t := ⟨s.x + t.x, s.z + t.z, s.phase + t.phase + signPhase (s.z ⬝ᵥ t.x)⟩

@[simp] lemma mul_x (s t : PauliString n) : (s * t).x = s.x + t.x := rfl
@[simp] lemma mul_z (s t : PauliString n) : (s * t).z = s.z + t.z := rfl

lemma mul_phase (s t : PauliString n) :
    (s * t).phase = s.phase + t.phase + signPhase (s.z ⬝ᵥ t.x) := rfl

/-- The identity operator. -/
instance : One (PauliString n) where one := ⟨0, 0, 0⟩

@[simp] lemma one_x : (1 : PauliString n).x = 0 := rfl
@[simp] lemma one_z : (1 : PauliString n).z = 0 := rfl
@[simp] lemma one_phase : (1 : PauliString n).phase = 0 := rfl

/-- The inverse. `star` below is *defined* to be this, and `star_eq_inv` is therefore `rfl`; the
theorem with content — that this really is the operator adjoint — is `toMatrix_star` in
`Pauli/Matrix.lean`. -/
instance : Inv (PauliString n) where
  inv s := ⟨s.x, s.z, -s.phase + signPhase (s.z ⬝ᵥ s.x)⟩

@[simp] lemma inv_x (s : PauliString n) : s⁻¹.x = s.x := rfl
@[simp] lemma inv_z (s : PauliString n) : s⁻¹.z = s.z := rfl

lemma inv_phase (s : PauliString n) :
    s⁻¹.phase = -s.phase + signPhase (s.z ⬝ᵥ s.x) := rfl

/-- The `n`-qubit **Pauli group**.

The group law is `(s * t).phase = s.phase + t.phase + signPhase (s.z ⬝ᵥ t.x)` on phases and
addition of bit vectors on the `x`- and `z`-parts; the inverse keeps the bit vectors and has
phase `-s.phase + signPhase (s.z ⬝ᵥ s.x)`.

At the revision pinned by this library Mathlib has no Pauli group, no Pauli matrices and no
`Anticommute` predicate. The Pauli group is *not* new to Lean: `Stavan-Jain/QECLean` carries
`NQubitPauliGroupElement`, a `Fin 4` phase over an inductive `{I,X,Y,Z}`-valued function, and
proves the same commute-or-anticommute dichotomy. It is prior art to read rather than a
dependency of this library. -/
instance : Group (PauliString n) where
  mul_assoc s t u := by
    refine ext' ?_ ?_ ?_
    · simp [add_assoc]
    · simp [add_assoc]
    · simp only [mul_phase, mul_z, mul_x, add_dotProduct, dotProduct_add, signPhase_add]
      ring
  one_mul s := by refine ext' ?_ ?_ ?_ <;> simp [mul_phase]
  mul_one s := by refine ext' ?_ ?_ ?_ <;> simp [mul_phase]
  inv_mul_cancel s := by
    refine ext' ?_ ?_ ?_
    · simpa using bits_add_self s.x
    · simpa using bits_add_self s.z
    · change -s.phase + signPhase (s.z ⬝ᵥ s.x) + s.phase + signPhase (s.z ⬝ᵥ s.x)
        = (1 : PauliString n).phase
      rw [show -s.phase + signPhase (s.z ⬝ᵥ s.x) + s.phase + signPhase (s.z ⬝ᵥ s.x)
          = signPhase (s.z ⬝ᵥ s.x) + signPhase (s.z ⬝ᵥ s.x) by ring]
      simp

/-! ### The adjoint -/

/-- The adjoint of a Pauli string, defined to be its group inverse. That this *is* the operator
adjoint is not an assumption: `Pauli/Matrix.lean` proves `star (toMatrix s) = toMatrix (star s)`
(`toMatrix_star`), which is where the content sits. -/
instance : Star (PauliString n) where star s := s⁻¹

/-- Pauli strings are **unitary**: the adjoint is the inverse. Definitional here, given how `star`
is defined; the theorem with content is `toMatrix_star`. -/
lemma star_eq_inv (s : PauliString n) : star s = s⁻¹ := rfl

instance : InvolutiveStar (PauliString n) where
  star_involutive s := inv_inv s

instance : StarMul (PauliString n) where
  star_mul s t := mul_inv_rev s t

/-! ### The symplectic form and the commutation dichotomy -/

/-- The symplectic form `⟪s,t⟫ = ∑ᵢ (x_s(i) z_t(i) + z_s(i) x_t(i))` over `ZMod 2`, written with
Mathlib's `dotProduct`. It is the obstruction to commuting: see
`commute_iff_sympForm_eq_zero`. -/
def sympForm (s t : PauliString n) : ZMod 2 := s.x ⬝ᵥ t.z + s.z ⬝ᵥ t.x

lemma sympForm_eq_sum (s t : PauliString n) :
    sympForm s t = ∑ i, (s.x i * t.z i + s.z i * t.x i) := by
  simp [sympForm, dotProduct, Finset.sum_add_distrib]

lemma sympForm_comm (s t : PauliString n) : sympForm s t = sympForm t s := by
  simp only [sympForm]
  rw [dotProduct_comm s.x t.z, dotProduct_comm s.z t.x, add_comm]

/-- The symplectic form is **bilinear on the right**: `⟪u, s t⟫ = ⟪u, s⟫ + ⟪u, t⟫`. -/
lemma sympForm_mul_right (u s t : PauliString n) :
    sympForm u (s * t) = sympForm u s + sympForm u t := by
  simp only [sympForm, mul_x, mul_z, dotProduct_add]
  ring

/-- The symplectic form is **bilinear on the left**. -/
lemma sympForm_mul_left (s t u : PauliString n) :
    sympForm (s * t) u = sympForm s u + sympForm t u := by
  simp only [sympForm, mul_x, mul_z, add_dotProduct]
  ring

/-- The form is alternating: every Pauli string commutes with itself. -/
@[simp] lemma sympForm_self (s : PauliString n) : sympForm s s = 0 := by
  simp only [sympForm]
  rw [dotProduct_comm s.x s.z]
  exact bit_add_self _

/-- `phaseMul k s` is `i^k · s`: the same bit vectors, the phase shifted by `k`. -/
def phaseMul (k : ZMod 4) (s : PauliString n) : PauliString n := ⟨s.x, s.z, s.phase + k⟩

@[simp] lemma phaseMul_x (k : ZMod 4) (s : PauliString n) : (phaseMul k s).x = s.x := rfl
@[simp] lemma phaseMul_z (k : ZMod 4) (s : PauliString n) : (phaseMul k s).z = s.z := rfl
@[simp] lemma phaseMul_phase (k : ZMod 4) (s : PauliString n) :
    (phaseMul k s).phase = s.phase + k := rfl

@[simp] lemma sympForm_phaseMul_right (k : ZMod 4) (s t : PauliString n) :
    sympForm s (phaseMul k t) = sympForm s t := rfl

@[simp] lemma sympForm_phaseMul_left (k : ZMod 4) (s t : PauliString n) :
    sympForm (phaseMul k s) t = sympForm s t := rfl

/-- **The partner still anticommutes with the generator**: `⟪G, G s⟫ = ⟪G, s⟫`, by bilinearity
and `⟪G, G⟫ = 0`. The proof of `apd:thm:local_flow_k_local` pairs each Pauli `s` anticommuting
with the generator with a partner `s' = ±i G s` and uses that `s'` is again a Hermitian Pauli
anticommuting with `G`. This lemma is the anticommutation half (the phase `±i` does not affect
`sympForm`, see `sympForm_phaseMul_right`); the Hermiticity half is
`isSelfAdjoint_phaseMul_one_mul`. -/
@[simp] lemma sympForm_mul_self_right (G s : PauliString n) :
    sympForm G (G * s) = sympForm G s := by
  rw [sympForm_mul_right, sympForm_self, zero_add]

@[simp] lemma phaseMul_zero (s : PauliString n) : phaseMul 0 s = s := by
  refine ext' rfl rfl ?_; simp

@[simp] lemma phaseMul_eq_phaseMul_iff {k l : ZMod 4} {s : PauliString n} :
    phaseMul k s = phaseMul l s ↔ k = l := by
  constructor
  · intro h
    have := congrArg PauliString.phase h
    simpa using this
  · rintro rfl; rfl

@[simp] lemma phaseMul_eq_self_iff {k : ZMod 4} {s : PauliString n} :
    phaseMul k s = s ↔ k = 0 := by
  constructor
  · intro h
    have := congrArg PauliString.phase h
    simpa using this
  · rintro rfl; simp

/-- **The exact commutation law.** Reversing a product multiplies it by `(-1)^{⟪s,t⟫}`. The two
cases of `apd:eq:pauli_rotation_branch`, commuting and anticommuting, are the two values of this
one sign. -/
theorem mul_eq_phaseMul_sympForm (s t : PauliString n) :
    s * t = phaseMul (signPhase (sympForm s t)) (t * s) := by
  refine ext' ?_ ?_ ?_
  · simp [add_comm]
  · simp [add_comm]
  · simp only [mul_phase, phaseMul_phase, sympForm, signPhase_add]
    rw [dotProduct_comm s.x t.z]
    rw [show t.phase + s.phase + signPhase (t.z ⬝ᵥ s.x)
          + (signPhase (t.z ⬝ᵥ s.x) + signPhase (s.z ⬝ᵥ t.x))
        = s.phase + t.phase + signPhase (s.z ⬝ᵥ t.x)
          + (signPhase (t.z ⬝ᵥ s.x) + signPhase (t.z ⬝ᵥ s.x)) by ring]
    simp

/-- Two Pauli strings commute exactly when the symplectic form vanishes. -/
theorem commute_iff_sympForm_eq_zero (s t : PauliString n) :
    Commute s t ↔ sympForm s t = 0 := by
  have h : Commute s t ↔ s * t = t * s := Iff.rfl
  rw [h, mul_eq_phaseMul_sympForm s t]
  constructor
  · intro hc
    have := (phaseMul_eq_self_iff (k := signPhase (sympForm s t)) (s := t * s)).1 hc
    simpa using this
  · intro hc; rw [hc]; simp

/-- Two Pauli strings anticommute exactly when the symplectic form is one. -/
theorem anticommute_iff_sympForm_eq_one (s t : PauliString n) :
    s * t = phaseMul 2 (t * s) ↔ sympForm s t = 1 := by
  rw [mul_eq_phaseMul_sympForm s t, phaseMul_eq_phaseMul_iff]
  exact (by decide : ∀ a : ZMod 2, signPhase a = 2 ↔ a = 1) _

/-- **The dichotomy is exhaustive.** The symplectic form takes only the values `0` and `1`, so
there is no third case beyond the two that `apd:eq:pauli_rotation_branch` lists. -/
theorem sympForm_eq_zero_or_one (s t : PauliString n) :
    sympForm s t = 0 ∨ sympForm s t = 1 :=
  (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) _

/-- **Any two Pauli strings either commute or anticommute.** This is the fact that makes the
two cases `[G,P] = 0` and `{G,P} = 0` of `apd:eq:pauli_rotation_branch` exhaustive, so that a
Pauli rotation acting on a Pauli operator either leaves it unchanged or splits it into exactly
two terms. Here anticommutation is spelled `s * t = phaseMul 2 (t * s)`, that is
`s t = i² · t s = −t s`.

This is the hypothesis-level companion to `Lean4LPD.rot_conj_of_commute` and
`Lean4LPD.rot_conj_of_anticommute`: those two theorems cover a commuting and an anticommuting
generator, and without this lemma nothing rules out a pair of Paulis that is neither.
`Pauli/Matrix.lean` transports it to operators as `toMatrix_commute_or_anticommute`, which is the
form `Rotation.lean` consumes. -/
theorem commute_or_anticommute (s t : PauliString n) :
    Commute s t ∨ s * t = phaseMul 2 (t * s) := by
  rcases sympForm_eq_zero_or_one s t with h | h
  · exact Or.inl ((commute_iff_sympForm_eq_zero s t).2 h)
  · exact Or.inr ((anticommute_iff_sympForm_eq_one s t).2 h)

/-! ### Hermitian Pauli strings -/

/-- **Hermiticity and involutivity coincide** for a Pauli string.

`Rotation.lean` needs both `G * G = 1` and `star G = G`, and in a general `*`-algebra the two are
**independent**: a self-adjoint element need not square to one (take `2` in `ℂ`), and an element
squaring to one need not be self-adjoint (take `!![1,1;0,-1]`). `Rotation.lean` notes the first of
those. For a Pauli string they coincide, because `star s = s⁻¹` (`star_eq_inv`): the string is
unitary, so self-adjointness *is* involutivity, and one hypothesis discharges both. -/
theorem isSelfAdjoint_iff_mul_self_eq_one {s : PauliString n} :
    IsSelfAdjoint s ↔ s * s = 1 := by
  rw [IsSelfAdjoint, star_eq_inv, inv_eq_iff_mul_eq_one]

/-- Hermiticity in coordinates: `i^{phase} X^x Z^z` is self-adjoint exactly when
`2·phase = 2⟪z,x⟫` in `ZMod 4` — equivalently, `phase ≡ ⟪z,x⟫ (mod 2)`, the standard criterion.

This fixes the parity of the phase and nothing more. Both solutions are admissible and they differ
by `2`, so a string and its negative are both self-adjoint; the criterion does not pick out a
canonical sign. -/
theorem isSelfAdjoint_iff_phase {s : PauliString n} :
    IsSelfAdjoint s ↔ signPhase (s.z ⬝ᵥ s.x) = 2 * s.phase := by
  rw [IsSelfAdjoint, star_eq_inv]
  constructor
  · intro h
    have hp := congrArg PauliString.phase h
    simp only [inv_phase] at hp
    calc signPhase (s.z ⬝ᵥ s.x)
        = s.phase + (-s.phase + signPhase (s.z ⬝ᵥ s.x)) := by ring
      _ = s.phase + s.phase := by rw [hp]
      _ = 2 * s.phase := by ring
  · intro h
    refine ext' rfl rfl ?_
    change -s.phase + signPhase (s.z ⬝ᵥ s.x) = s.phase
    rw [h]; ring

/-- **The partner Pauli `i G s` is again Hermitian**, for Hermitian `G` and `s` with
`⟪G,s⟫ = 1`. Together with `sympForm_mul_self_right` this is the property of the partner
`s' = ±i G s` used in the proof of `apd:thm:local_flow_k_local`.

It is needed for the anticommuting branch to mean anything physically:
`cos(dt) s + i sin(dt) G s` is an observable only if `i G s` is. Note the Hermitian Pauli strings
are *not* closed under multiplication — `G s` itself is anti-Hermitian when `G` and `s`
anticommute, which is exactly why the partner carries the factor `i`. -/
theorem isSelfAdjoint_phaseMul_one_mul {G s : PauliString n} (hG : IsSelfAdjoint G)
    (hs : IsSelfAdjoint s) (h : sympForm G s = 1) : IsSelfAdjoint (phaseMul 1 (G * s)) := by
  rw [isSelfAdjoint_iff_phase] at hG hs ⊢
  have e1 : signPhase (G.z ⬝ᵥ s.x) + signPhase (s.z ⬝ᵥ G.x) = 2 := by
    rw [← signPhase_add, add_comm (G.z ⬝ᵥ s.x) _, dotProduct_comm s.z G.x]
    rw [show G.x ⬝ᵥ s.z + G.z ⬝ᵥ s.x = sympForm G s from rfl, h, signPhase_one]
  have e2 : 2 * signPhase (G.z ⬝ᵥ s.x) = 0 := two_mul_signPhase _
  simp only [phaseMul_x, phaseMul_z, phaseMul_phase, mul_x, mul_z, mul_phase,
    add_dotProduct, dotProduct_add, signPhase_add]
  linear_combination hG + hs + e1 - e2

/-- A Pauli string with neither an `X`- nor a `Z`-part is a phase, and a phase commutes with
everything. Contrapositively: anything that anticommutes with some `t` has a non-trivial `X`- or
`Z`-part. No self-adjointness is involved. -/
theorem sympForm_eq_zero_of_x_eq_zero_of_z_eq_zero {s t : PauliString n}
    (hx : s.x = 0) (hz : s.z = 0) : sympForm s t = 0 := by
  simp [sympForm, hx, hz]

/-! ### Witnesses

Concrete elements, so that no hypothesis in this development is satisfiable only in principle.
This matters twice over: `sympForm G s = 1` is the hypothesis of every sharp weight bound and of
the anticommuting branch, and at `n = 0` it is **unsatisfiable** — `Fin 0 → ZMod 2` is a singleton,
every `x` and `z` is `0`, and `sympForm` is identically zero, so the whole anticommuting branch is
vacuous there. One qubit is enough to make it non-vacuous. -/

/-- The one-qubit `X`. -/
def X1 : PauliString 1 := ⟨1, 0, 0⟩

/-- The one-qubit `Z`. -/
def Z1 : PauliString 1 := ⟨0, 1, 0⟩

/-- The one-qubit `Y`, whose phase is one of the two `isSelfAdjoint_iff_phase` admits. It is `+Y`
rather than `−Y`; `Pauli/Matrix.lean` checks that entrywise. -/
def Y1 : PauliString 1 := ⟨1, 1, 1⟩

theorem isSelfAdjoint_X1 : IsSelfAdjoint X1 := isSelfAdjoint_iff_phase.2 (by decide)

theorem isSelfAdjoint_Z1 : IsSelfAdjoint Z1 := isSelfAdjoint_iff_phase.2 (by decide)

theorem isSelfAdjoint_Y1 : IsSelfAdjoint Y1 := isSelfAdjoint_iff_phase.2 (by decide)

/-- **`X` and `Z` anticommute**, so the anticommuting branch has a witness and every theorem
conditioned on `sympForm G s = 1` says something. -/
theorem sympForm_X1_Z1 : sympForm X1 Z1 = 1 := by decide

/-- `i` times their product is the Hermitian partner `Y`, as `isSelfAdjoint_phaseMul_one_mul`
predicts. The bare product is not: `X Z = −i Y`. -/
theorem phaseMul_one_X1_mul_Z1 : phaseMul 1 (X1 * Z1) = Y1 := by decide

end PauliString

end Lean4LPD
