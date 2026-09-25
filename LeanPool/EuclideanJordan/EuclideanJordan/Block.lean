/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.EuclideanJordan.EuclideanJordan.Frame



/-!
# The rank-two block, split into its three Peirce pieces

For orthogonal idempotents `p, q`, the Peirce-1 space of the rank-two block `q' = p + q`
decomposes:

  `J₁(p + q) = J₁(p) ⊕ (J_{1/2}(p) ∩ J_{1/2}(q)) ⊕ J₁(q)`.

`exists_block_split` is the forward half and `block_mul_eq_self` the converse, so together
they characterise `J₁(p+q)` exactly. This is the Faraut–Korányi coherence-block structure at
the smallest interesting size.

## The argument

`L_p` commutes with `L_q` (`opCommute_of_orthogonal`), so `L_p` commutes with `L_{p+q}`, so
**`L_{p+q}` commutes with every polynomial in `L_p`** — and the three Peirce projections of
`p` are such polynomials, hence they all preserve `J₁(p+q)`.
★ The subject of that chain shifts, and an earlier draft let it shift silently ("…hence with
every polynomial in `L_p`", with `L_p` still the subject, which is trivially true and not what
is meant). Caught on the arc's second audit pass; a true sentence whose grammar names the
wrong subject is the same defect kind as a true conclusion with a false reason. Apply
them to `x ∈ J₁(p+q)`: the pieces have `p`-eigenvalues `1`, `1/2`, `0`, and since
`q ∘ z = (p+q) ∘ z − p ∘ z = z − p ∘ z` on `J₁(p+q)`, their `q`-eigenvalues are the
complements `0`, `1/2`, `1`. **The three admissible patterns are exactly the three ways
`μ + ν = 1` can happen with `μ, ν ∈ {0, 1/2, 1}`** — which is why the block has three pieces
and not nine.

★ **The eigenvalue trichotomy is what makes this finite**, but note it is not *invoked*: the
projections do the work directly. The trichotomy explains the shape of the answer rather than
appearing in the proof.

## `q` is not assumed idempotent, and that is not an oversight

`exists_block_split` needs only **`p ∘ p = p` and `p ∘ q = 0`**. Lean's unused-variable linter
caught the `hq` hypothesis being dead and it was removed rather than silenced. The reason is
visible in the argument above: every claim about `q` is derived from
`q ∘ z = (p+q) ∘ z − p ∘ z`, which never asks what `q ∘ q` is.

★ What `hq` buys is the *interpretation*: without it `p + q` need not be idempotent, so
"`J₁(p+q)`" is not a Peirce space and "`J₁(q)`" is not either — the conclusions are still true,
they just stop being a Peirce decomposition. Callers wanting the FK reading should have `hq`
in hand from `IsOrthIdemFamily`; the theorem simply does not need to be told.
-/

@[expose] public section

namespace EuclideanJordan

section Block

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J]

omit [IsCommJordan J] in
/-- If `L_c` commutes with `L_p` then it commutes with the Peirce-1 projection of `p`. -/
theorem mul_peirceOne_comm {c p : J} (h : ∀ w : J, c * (p * w) = p * (c * w)) (x : J) :
    c * peirceOne p x = peirceOne p (c * x) := by
  simp only [peirceOne_apply, mul_sub, mul_smul_comm', h]

omit [IsCommJordan J] in
/-- The same for the Peirce-`1/2` projection. -/
theorem mul_peirceHalf_comm {c p : J} (h : ∀ w : J, c * (p * w) = p * (c * w)) (x : J) :
    c * peirceHalf p x = peirceHalf p (c * x) := by
  simp only [peirceHalf_apply, mul_sub, mul_smul_comm', h]

omit [IsCommJordan J] in
/-- The same for the Peirce-`0` projection. -/
theorem mul_peirceZero_comm {c p : J} (h : ∀ w : J, c * (p * w) = p * (c * w)) (x : J) :
    c * peirceZero p x = peirceZero p (c * x) := by
  simp only [peirceZero_apply, mul_add, mul_sub, mul_smul_comm', h]

variable {p q : J}

omit [IsScalarTower ℝ J J] in
/-- `L_{p+q}` commutes with `L_p`, for `p` idempotent and orthogonal to `q`. -/
theorem add_mul_comm_left (hp : p * p = p) (hpq : p * q = 0) (w : J) :
    (p + q) * (p * w) = p * ((p + q) * w) := by
  rw [add_mul, add_mul, mul_add, opCommute_of_orthogonal hp hpq w]

/-- **The rank-two block splits.** Every element of `J₁(p+q)` is the sum of an element of
`J₁(p)`, an element of the coherence space `J_{1/2}(p) ∩ J_{1/2}(q)`, and an element of
`J₁(q)` — and the `q`-eigenvalues come out as the complements of the `p`-eigenvalues.

★ Needs only `p ∘ p = p` and `p ∘ q = 0`; see the module docstring on why `q ∘ q = q` is not
required. -/
theorem exists_block_split (hp : p * p = p) (hpq : p * q = 0) {x : J} (hx : (p + q) * x = x) :
    ∃ a b c : J, (p * a = a ∧ q * a = 0) ∧ (p * b = (2 : ℝ)⁻¹ • b ∧ q * b = (2 : ℝ)⁻¹ • b)
      ∧ (p * c = 0 ∧ q * c = c) ∧ x = a + b + c := by
  have hcomm := add_mul_comm_left hp hpq
  refine ⟨peirceOne p x, peirceHalf p x, peirceZero p x, ⟨mul_peirceOne hp x, ?_⟩,
    ⟨mul_peirceHalf hp x, ?_⟩, ⟨mul_peirceZero hp x, ?_⟩, (peirce_add_add p x).symm⟩
  · have h1 : p * peirceOne p x + q * peirceOne p x = peirceOne p x := by
      rw [← add_mul, mul_peirceOne_comm hcomm x, hx]
    rw [mul_peirceOne hp x] at h1
    refine add_left_cancel (a := peirceOne p x) ?_
    rw [add_zero]
    exact h1
  · have h2 : p * peirceHalf p x + q * peirceHalf p x = peirceHalf p x := by
      rw [← add_mul, mul_peirceHalf_comm hcomm x, hx]
    rw [mul_peirceHalf hp x] at h2
    have hstep : q * peirceHalf p x = peirceHalf p x - (2 : ℝ)⁻¹ • peirceHalf p x :=
      eq_sub_of_add_eq (by rw [add_comm]; exact h2)
    rw [hstep]
    module
  · have h3 : p * peirceZero p x + q * peirceZero p x = peirceZero p x := by
      rw [← add_mul, mul_peirceZero_comm hcomm x, hx]
    rw [mul_peirceZero hp x, zero_add] at h3
    exact h3

omit [IsCommJordan J] [IsScalarTower ℝ J J] in
/-- **The converse.** Each of the three admissible eigenvalue patterns lands in `J₁(p+q)`, so
together with `exists_block_split` this characterises the block exactly.

The three cases are `1 + 0`, `1/2 + 1/2` and `0 + 1` — the only ways two elements of
`{0, 1/2, 1}` sum to `1`. -/
theorem block_mul_eq_self {z : J} (h : (p * z = z ∧ q * z = 0)
    ∨ (p * z = (2 : ℝ)⁻¹ • z ∧ q * z = (2 : ℝ)⁻¹ • z) ∨ (p * z = 0 ∧ q * z = z)) :
    (p + q) * z = z := by
  rw [add_mul]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, add_zero]
  · rw [h1, h2]; module
  · rw [h1, h2, zero_add]

/-! ### The Peirce projections of orthogonal idempotents commute

`EuclideanJordan/PeirceMul.lean` named this as the ingredient missing for the frame-level joint
decomposition: *"closing the field needs the joint Peirce decomposition over a frame, which
needs these rules plus the commutation of the projections of distinct frame idempotents."*
Here it is.

The generic lemmas below take **any** linear `F` commuting with `L_q` and conclude that `F`
commutes with each Peirce projection of `q`. Instantiating `F` at a Peirce projection of `p`
gives all nine commutations; the three diagonal ones are named, and the mixed six are one
line each from the same lemmas. -/

section ProjComm

omit [IsCommJordan J] in
/-- A linear map commuting with `L_q` commutes with `q`'s Peirce-1 projection. -/
theorem peirceOne_comm_of_mul_comm {q : J} {F : J →ₗ[ℝ] J} (h : ∀ w, q * F w = F (q * w))
    (x : J) : peirceOne q (F x) = F (peirceOne q x) := by
  simp only [peirceOne_apply, h, map_sub, map_smul]

omit [IsCommJordan J] in
/-- The same for the Peirce-`1/2` projection. -/
theorem peirceHalf_comm_of_mul_comm {q : J} {F : J →ₗ[ℝ] J} (h : ∀ w, q * F w = F (q * w))
    (x : J) : peirceHalf q (F x) = F (peirceHalf q x) := by
  simp only [peirceHalf_apply, h, map_sub, map_smul]

omit [IsCommJordan J] in
/-- The same for the Peirce-`0` projection. -/
theorem peirceZero_comm_of_mul_comm {q : J} {F : J →ₗ[ℝ] J} (h : ∀ w, q * F w = F (q * w))
    (x : J) : peirceZero q (F x) = F (peirceZero q x) := by
  simp only [peirceZero_apply, h, map_add, map_sub, map_smul]

/-- For orthogonal idempotents, `L_q` commutes with `p`'s Peirce-1 projection. -/
theorem mul_peirceOne_comm_orth (hq : q * q = q) (hpq : p * q = 0) (x : J) :
    q * peirceOne p x = peirceOne p (q * x) :=
  mul_peirceOne_comm (fun w => opCommute_of_orthogonal hq (by rw [mul_comm]; exact hpq) w) x

/-- For orthogonal idempotents, `L_q` commutes with `p`'s Peirce-`1/2` projection. -/
theorem mul_peirceHalf_comm_orth (hq : q * q = q) (hpq : p * q = 0) (x : J) :
    q * peirceHalf p x = peirceHalf p (q * x) :=
  mul_peirceHalf_comm (fun w => opCommute_of_orthogonal hq (by rw [mul_comm]; exact hpq) w) x

/-- For orthogonal idempotents, `L_q` commutes with `p`'s Peirce-`0` projection. -/
theorem mul_peirceZero_comm_orth (hq : q * q = q) (hpq : p * q = 0) (x : J) :
    q * peirceZero p x = peirceZero p (q * x) :=
  mul_peirceZero_comm (fun w => opCommute_of_orthogonal hq (by rw [mul_comm]; exact hpq) w) x

/-- **The Peirce-1 projections of orthogonal idempotents commute.** -/
theorem peirceOne_comm_peirceOne (hq : q * q = q) (hpq : p * q = 0) (x : J) :
    peirceOne q (peirceOne p x) = peirceOne p (peirceOne q x) :=
  peirceOne_comm_of_mul_comm (F := peirceOne p) (mul_peirceOne_comm_orth hq hpq) x

/-- **The Peirce-`1/2` projections of orthogonal idempotents commute** — the projection onto
the coherence space is well defined independently of which idempotent is applied first. -/
theorem peirceHalf_comm_peirceHalf (hq : q * q = q) (hpq : p * q = 0) (x : J) :
    peirceHalf q (peirceHalf p x) = peirceHalf p (peirceHalf q x) :=
  peirceHalf_comm_of_mul_comm (F := peirceHalf p) (mul_peirceHalf_comm_orth hq hpq) x

/-- **The Peirce-`0` projections of orthogonal idempotents commute.** -/
theorem peirceZero_comm_peirceZero (hq : q * q = q) (hpq : p * q = 0) (x : J) :
    peirceZero q (peirceZero p x) = peirceZero p (peirceZero q x) :=
  peirceZero_comm_of_mul_comm (F := peirceZero p) (mul_peirceZero_comm_orth hq hpq) x

end ProjComm

end Block

end EuclideanJordan
