/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.Ladder.Defs
public import LeanPool.LowWeightPauliDynamics.Ladder.Weighted
public import LeanPool.LowWeightPauliDynamics.Pauli.Branch
public import LeanPool.LowWeightPauliDynamics.Pauli.Coeff

/-!
# The damped local norm flow, and the Pauli inhabitant of `Ladder`

This file proves `apd:thm:local_flow_k_local`, the damped local norm flow on which the
quantitative truncation-error analysis of LPD rests:

  `N_{≥m}^{(g)} ≤ N_{≥m}^{(g-1)} + sin(dt)·N_{≥m-1}^{(g-1)}`.

Here `N_{≥m}^{(g)}` is the high-weight norm (`apd:eq:def_high_weight_norm`) of the observable
after `g` Pauli rotations, taken above the rung weight `w_m = k_o + (m-1)(k_h-1)`. The file then
uses the inequality to construct an instance of the abstract structure `Lean4LPD.Ladder`, whose
`step` field is exactly this recursion. The consequences of the recursion are proved in `Ladder/`
for an abstract ladder, with no Pauli infrastructure, so the instance is what makes them apply to
the Pauli model.

## Main definitions

* `PauliString.partner`, `PauliString.partnerSign`: the pairing `s ↔ ±i G s` of the classes that
  anticommute with `G`, and the sign relating `i G s` to the self-adjoint representative `herm`.
* `PauliString.rotAct`: the action of conjugation by one Pauli rotation on coefficient vectors.
* `PauliString.traj`: the Heisenberg trajectory `O^{(g)} = U_g† O U_g`.
* `PauliString.ladderN`: the family `N m g` of high-weight norms along the trajectory.
* `PauliString.pauliLadder`, `PauliString.pauliWeightedLadder`, `PauliString.pauliLadderOfHerm`:
  the instances of `Ladder` and `WeightedLadder`.

## Main results

* `PauliString.coeffVec_conj`: conjugation by one rotation acts on coefficient vectors as
  `rotAct`.
* `PauliString.norm_rotAct`: `rotAct` is an isometry of `ℓ²`.
* `PauliString.norm_restr_high_rotAct_low`: the inflow into the high-weight region is at most
  `|sin θ|` times the mass on the partners.
* `PauliString.highNorm_conj_le_highNorm`, `PauliString.local_flow_k_local`:
  `apd:thm:local_flow_k_local` for one rotation, at general thresholds and at the rung weights.
* `PauliString.highNorm_conj_le_pauliNorm`: the form used at rung `1`, with the total mass on the
  right.
* `PauliString.pauliNorm_conj`, `PauliString.pauliNorm_traj`: unitary invariance of the Pauli
  2-norm.
* `PauliString.highNorm_restr_le`: restriction (truncation) only decreases high-weight norms.

The one-rotation theorems assume only that the generator is a Hermitian Pauli string of weight at
most `k_h`; they hold for every operator `O` and every angle. In particular no locality hypothesis
on the observable is needed, which is stronger than the paper's statement. Locality of the initial
observable enters only through the `init` field of `pauliLadder`.

## The argument

The proof follows the paper's, in four moves.

1. **The coefficient vector** — `Pauli/Coeff.lean`, with `‖O‖_{2,normalized} = ‖x‖_{ℓ²}`.
2. **Conjugation acts as a real orthogonal matrix `A`**: commuting classes are fixed,
   anticommuting ones pair up as `s ↔ ±i G s`, and `A` is a planar rotation on each pair. Here
   that is `rotAct`, and it is a *theorem* about the coefficients (`coeffVec_conj`) rather than a
   description: `Pauli/Branch.lean`'s `pauli_rotation_branch_anticommute_hermitian` supplies the
   operator identity (`apd:eq:pauli_rotation_branch`), trace cyclicity moves the conjugation onto
   the Pauli, and `partnerSign` is the sign of `±i G s`, which becomes part of the matrix entry.
   Orthogonality is `norm_rotAct`.
3. **`‖A_RR‖ ≤ 1`**: a submatrix of an orthogonal matrix has operator norm at most one.
   `BlockNorm.lean` proves exactly that statement, but it is not what is used here: no matrix `A`
   is ever built, so the corresponding step is
   `‖restr R (rotAct G θ v)‖ ≤ ‖rotAct G θ v‖ = ‖v‖`, i.e. `norm_restr_le` composed with the
   isometry. Same content, one fewer object.
4. **The inflow `‖A_RB x_B‖ ≤ sin(dt)·N_{≥m-1}`** — `norm_restr_high_rotAct_low`.
   The weight step is `weight_le_weight_mul_add_kh`, whose `k_h − 1` (rather than `k_h`) holds only
   because the pairing is between *anticommuting* Paulis; see `Pauli/Weight.lean`.

Minkowski's inequality is `norm_add_le` on `EuclideanSpace`.

## What is proved, and what is assumed

`local_flow_k_local` is the inequality for one rotation at rung `m ≥ 2`, in the variables
`w_m = k_o + (m-1)(k_h-1)`. `pauliLadder` is the `Ladder` instance, hence the inequality along a
whole trajectory, at every rung, and `pauliWeightedLadder` is the same family as a
`WeightedLadder`. **`MultiLadder` is not inhabited here**: its `step` is the multi-jump recursion
of `apd:thm:layer_inflow`, about a layer of disjointly supported rotations; that instance is
`pauliMultiLadder` in `Pauli/LayerLadder.lean`.

Three things to read narrowly.

* **`a` is `|sin(dt)|`, not `sin(dt)`.** `pauliLadder` takes any `a` dominating every
  `|sin(θ_g)|`, which is what the estimate gives with no sign hypothesis on the angles.
* **Rung `0` is the reservoir, not `rungWeight ko kh 0`.** `Ladder/Defs.lean` explains why:
  truncated `ℕ` subtraction makes `rungWeight ko kh 0 = k_o`, whereas the model wants
  `w_0 = k_o - (k_h-1)`. So `ladderN` sets `N 0 g := ‖O^{(g)}‖_{2,normalized}`, which satisfies
  `reservoir`
  with equality by unitary invariance (`pauliNorm_traj`; this is the base case of
  `apd:cor:norm_cumulation_jump`). `step` at `m = 1` is then `highNorm_conj_le_pauliNorm`, which
  bounds the inflow by the total mass. Since the total mass dominates every high-weight norm
  (`highNorm_le_pauliNorm`), this reading makes `step` at `m = 1` *weaker* than the flow bound
  with a genuine weight threshold `w_0` on the right, and unlike that bound it needs no condition
  relating `k_o` and `k_h`.
* **The trajectory here carries no truncation.** Truncation zeroes coefficients and so only
  decreases every `N_{≥m}`, which is why `apd:cor:norm_cumulation_jump` holds along the truncated
  LPD trajectory as well. `highNorm_restr_le` is that statement on the coefficient side, but
  `traj` itself is the untruncated `U_g† O U_g`; the truncated trajectory and its ladder are in
  `Pauli/Truncate.lean`.

The flow is stated with the closed-form rotation `rot` and the entrywise Pauli matrices
`toMatrix`. That `rot` is the matrix exponential and that `toMatrix` is the correctly phased tensor
product are proved separately, in `RotationExp.lean` and `Pauli/Tensor.lean`.

The coefficient vector in the paper's proof is real. That is not formalized as a property of the
scalars: `coeff O p : ℂ`. It is not needed — the transformation is by real planar rotations, and
`∑ |x_p|²` is preserved for the same reason `∑ x_p²` would be. What *is* used is that the partner
`i G s` is a **Hermitian** Pauli (`isSelfAdjoint_phaseMul_one_mul`), which is what makes the
coefficient `sin θ` on it real.
-/

@[expose] public section

namespace Lean4LPD

open Finset

namespace PauliString

variable {n : ℕ} {G : PauliString n} {p : PauliIndex n} {kh w w' : ℕ}

private lemma le_of_sq_le_sq' {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith

private lemma add_ofLp (y z : EuclideanSpace ℂ (PauliIndex n)) (q : PauliIndex n) :
    (y + z).ofLp q = y.ofLp q + z.ofLp q := rfl

/-! ### The partner pairing on classes

In the proof of `apd:thm:local_flow_k_local` the Paulis that anticommute with the generator `G`
are grouped into unordered pairs `{s, s'}`, where `s' = ±i G s` is the partner of `s`, determined
up to sign. On classes that pairing is the translation `p ↦ (G.x + p.x, G.z + p.z)`, and it is an
involution because the `X`- and `Z`-parts live in characteristic two. -/

/-- The **partner class** of `p` under `G`: the class of `G · herm p`, hence of the partner
`±i G s` of `s = herm p`. -/
def partner (G : PauliString n) (p : PauliIndex n) : PauliIndex n := (G.x + p.1, G.z + p.2)

@[simp] lemma cls_mul_herm (G : PauliString n) (p : PauliIndex n) :
    cls (G * herm p) = partner G p := rfl

/-- The pairing is an **involution**, which is what lets `{s, s'}` be an unordered pair at all.
That it has no fixed point on the anticommuting sector is also true — a fixed point
would make `G` a phase, which commutes with everything — but it is not proved here and not needed:
`Finset.sum_involution` discharges a fixed point on its own, since `f p + f p = 0` forces
`f p = 0`. -/
@[simp] lemma partner_partner (G : PauliString n) (p : PauliIndex n) :
    partner G (partner G p) = p := by
  have h : ∀ u v : Bits n, u + (u + v) = v := fun u v => by
    rw [← add_assoc, bits_add_self, zero_add]
  exact Prod.ext (h G.x p.1) (h G.z p.2)

lemma partner_injective (G : PauliString n) : Function.Injective (partner G) := fun a b hab => by
  rw [← partner_partner G a, hab, partner_partner]

/-- **The partner still anticommutes with the generator**, stated on classes: `G` has the same
symplectic form with the partner of `p` as with `p`. This is what makes the pairing preserve the
anticommuting sector. -/
@[simp] lemma sympForm_herm_partner (G : PauliString n) (p : PauliIndex n) :
    sympForm G (herm (partner G p)) = sympForm G (herm p) := by
  have h : sympForm G (herm (partner G p)) = sympForm G (G * herm p) := rfl
  rw [h, sympForm_mul_self_right]

/-- The partner class has the weight of the product `G · herm p`, which is what
`Pauli/Weight.lean`'s bounds are about. -/
lemma wt_partner (G : PauliString n) (p : PauliIndex n) :
    wt (partner G p) = weight (G * herm p) := weight_congr rfl rfl

/-! ### The sign absorbed into the matrix entry

The partner of `s` is `i G s` only up to a sign, which depends on the representative chosen in
the partner's class; that sign becomes part of the matrix entry of the planar rotation.
`partnerSign` is that sign, and `partnerSign_partner` is the antisymmetry that makes the planar
rotation on the pair `{s, s'}` an *orthogonal* map rather than merely a bounded one. -/

/-- The sign relating the Hermitian partner `i G s` to the canonical self-adjoint representative
of its class: `toMatrix (i G herm p) = partnerSign G p • toMatrix (herm (partner G p))`. -/
noncomputable def partnerSign (G : PauliString n) (p : PauliIndex n) : ℂ :=
  iPow ((phaseMul 1 (G * herm p)).phase - (herm (partner G p)).phase)

/-- The defining property of `partnerSign`. -/
lemma toMatrix_partner (G : PauliString n) (p : PauliIndex n) :
    toMatrix (phaseMul 1 (G * herm p))
      = partnerSign G p • toMatrix (herm (partner G p)) := by
  rw [partnerSign, ← toMatrix_phaseMul]
  refine congrArg toMatrix (ext' rfl rfl ?_)
  change (phaseMul 1 (G * herm p)).phase
    = (herm (partner G p)).phase
      + ((phaseMul 1 (G * herm p)).phase - (herm (partner G p)).phase)
  ring

/-- `partnerSign` is a **sign**: the two self-adjoint representatives of a class differ by `±1`
(`phase_sub_of_isSelfAdjoint`), and `i G s` is self-adjoint when `G` and `s` are self-adjoint and
anticommute (`isSelfAdjoint_phaseMul_one_mul`). -/
lemma partnerSign_eq_one_or_neg_one (hG : IsSelfAdjoint G) (h : sympForm G (herm p) = 1) :
    partnerSign G p = 1 ∨ partnerSign G p = -1 := by
  have hs : IsSelfAdjoint (phaseMul 1 (G * herm p)) :=
    isSelfAdjoint_phaseMul_one_mul hG (isSelfAdjoint_herm p) h
  rcases phase_sub_of_isSelfAdjoint hs (isSelfAdjoint_herm (partner G p)) rfl rfl with hd | hd
  · exact Or.inl (by rw [partnerSign, hd, iPow_zero])
  · exact Or.inr (by rw [partnerSign, hd, iPow_two])

lemma partnerSign_mul_self (hG : IsSelfAdjoint G) (h : sympForm G (herm p) = 1) :
    partnerSign G p * partnerSign G p = 1 := by
  rcases partnerSign_eq_one_or_neg_one hG h with hp | hp <;> rw [hp] <;> ring

lemma norm_partnerSign (hG : IsSelfAdjoint G) (h : sympForm G (herm p) = 1) :
    ‖partnerSign G p‖ = 1 := by
  rcases partnerSign_eq_one_or_neg_one hG h with hp | hp <;> rw [hp] <;> simp

lemma conj_partnerSign (hG : IsSelfAdjoint G) (h : sympForm G (herm p) = 1) :
    (starRingEnd ℂ) (partnerSign G p) = partnerSign G p := by
  rcases partnerSign_eq_one_or_neg_one hG h with hp | hp <;> rw [hp] <;> simp

/-- **The signs on a pair are opposite.** The map `s ↦ i G s` squares to `-1`, not to the
identity: `i G (i G s) = -s`. Consequently the two entries of the planar rotation on `{s, s'}`
carry opposite signs, which is exactly what makes it a rotation. -/
lemma partnerSign_partner (hG : IsSelfAdjoint G) (h : sympForm G (herm p) = 1) :
    partnerSign G (partner G p) = -partnerSign G p := by
  have hph : ∀ r : PauliIndex n, (phaseMul 1 (G * herm r)).phase
      = G.phase + (herm r).phase + signPhase (G.z ⬝ᵥ r.1) + 1 := fun _ => rfl
  have hsp : signPhase (G.z ⬝ᵥ (partner G p).1)
      = signPhase (G.z ⬝ᵥ G.x) + signPhase (G.z ⬝ᵥ p.1) := by
    change signPhase (G.z ⬝ᵥ (G.x + p.1)) = _
    rw [dotProduct_add, signPhase_add]
  have hG' : signPhase (G.z ⬝ᵥ G.x) = 2 * G.phase := isSelfAdjoint_iff_phase.1 hG
  have hs2 : signPhase (G.z ⬝ᵥ p.1) + signPhase (G.z ⬝ᵥ p.1) = 0 := signPhase_add_self _
  have h4 : ∀ x : ZMod 4, 2 * x + 2 * x = 0 := by decide
  have hsum : ((phaseMul 1 (G * herm (partner G p))).phase
        - (herm (partner G (partner G p))).phase)
      + ((phaseMul 1 (G * herm p)).phase - (herm (partner G p)).phase) = 2 := by
    rw [partner_partner, hph, hph, hsp]
    linear_combination hG' + h4 G.phase + hs2
  have hmul : partnerSign G (partner G p) * partnerSign G p = -1 := by
    rw [partnerSign, partnerSign, ← iPow_add, hsum, iPow_two]
  calc partnerSign G (partner G p)
      = partnerSign G (partner G p) * (partnerSign G p * partnerSign G p) := by
        rw [partnerSign_mul_self hG h, mul_one]
    _ = partnerSign G (partner G p) * partnerSign G p * partnerSign G p := by ring
    _ = -partnerSign G p := by rw [hmul]; ring

/-! ### Conjugation as an orthogonal map `A` on coefficient vectors -/

/-- **The orthogonal matrix `A`** of the proof of `apd:thm:local_flow_k_local`, as a map on
coefficient vectors (no matrix is built): the identity on classes commuting with `G`, and the
planar rotation `x_s ↦ cos(θ)x_s ∓ sin(θ)x_{s'}` on each anticommuting pair, with the sign given
by `partnerSign`. That this *is* conjugation is `coeffVec_conj`; that it is *orthogonal* is
`norm_rotAct`. -/
noncomputable def rotAct (G : PauliString n) (θ : ℝ) (y : EuclideanSpace ℂ (PauliIndex n)) :
    EuclideanSpace ℂ (PauliIndex n) :=
  WithLp.toLp 2 fun p =>
    if sympForm G (herm p) = 0 then y.ofLp p
    else (Real.cos θ : ℂ) * y.ofLp p
      - (Real.sin θ : ℂ) * (partnerSign G p * y.ofLp (partner G p))

@[simp] lemma rotAct_apply (G : PauliString n) (θ : ℝ) (y : EuclideanSpace ℂ (PauliIndex n))
    (p : PauliIndex n) :
    (rotAct G θ y).ofLp p
      = if sympForm G (herm p) = 0 then y.ofLp p
        else (Real.cos θ : ℂ) * y.ofLp p
          - (Real.sin θ : ℂ) * (partnerSign G p * y.ofLp (partner G p)) := rfl

lemma rotAct_add (G : PauliString n) (θ : ℝ) (y z : EuclideanSpace ℂ (PauliIndex n)) :
    rotAct G θ (y + z) = rotAct G θ y + rotAct G θ z := by
  ext q
  simp only [rotAct_apply, add_ofLp]
  split <;> ring

/-- **Conjugation by one rotation acts on the coefficient vector as `A`**,
coefficient by coefficient.

Trace cyclicity moves the conjugation from `O` onto the Pauli, where
`pauli_rotation_branch_anticommute_hermitian` (`apd:eq:pauli_rotation_branch`, in its
Hermitian-partner form) applies at angle `-θ`. -/
theorem coeff_conj (hG : IsSelfAdjoint G) (θ : ℝ) (O : Matrix (Bits n) (Bits n) ℂ)
    (p : PauliIndex n) :
    coeff (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ)) p
      = if sympForm G (herm p) = 0 then coeff O p
        else (Real.cos θ : ℂ) * coeff O p
          - (Real.sin θ : ℂ) * (partnerSign G p * coeff O (partner G p)) := by
  have hcyc : (toMatrix (herm p) * (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ))).trace
      = (rot (toMatrix G) (-θ) * toMatrix (herm p) * rot (toMatrix G) θ * O).trace := by
    rw [show toMatrix (herm p) * (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ))
        = toMatrix (herm p) * rot (toMatrix G) θ * O * rot (toMatrix G) (-θ) by
          simp only [mul_assoc], Matrix.trace_mul_comm]
    simp only [mul_assoc]
  rw [coeff, hcyc]
  rcases sympForm_eq_zero_or_one G (herm p) with h | h
  · rw [ite_eq_left h]
    have hbr := pauli_rotation_branch_commute hG h (-θ)
    rw [neg_neg] at hbr
    rw [hbr, coeff]
  · rw [ite_eq_right (by rw [h]; decide : ¬ sympForm G (herm p) = 0)]
    have hbr := pauli_rotation_branch_anticommute_hermitian hG h (-θ)
    rw [neg_neg, Real.cos_neg, Real.sin_neg] at hbr
    rw [hbr, toMatrix_partner, Matrix.add_mul, Matrix.trace_add]
    simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [coeff, coeff]
    push_cast
    ring

/-- `coeff_conj` as a statement about the vector. -/
theorem coeffVec_conj (hG : IsSelfAdjoint G) (θ : ℝ) (O : Matrix (Bits n) (Bits n) ℂ) :
    coeffVec (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ)) = rotAct G θ (coeffVec O) := by
  ext p
  rw [coeffVec_apply, rotAct_apply, coeff_conj hG θ O p]
  simp only [coeffVec_apply]

/-! ### `A` is orthogonal

The pairs `{s, s'}` partition the anticommuting sector, so the sum of `|x_p|²` splits into the
fixed classes and the pairs, and on each pair the cross term cancels because `partnerSign` is
antisymmetric. -/

private lemma sum_anti_norm_sq (hG : IsSelfAdjoint G) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ∑ q ∈ univ.filter fun q : PauliIndex n => ¬ sympForm G (herm q) = 0,
        ‖(rotAct G θ y).ofLp q‖ ^ 2
      = ∑ q ∈ univ.filter fun q : PauliIndex n => ¬ sympForm G (herm q) = 0,
          ‖y.ofLp q‖ ^ 2 := by
  classical
  set A : Finset (PauliIndex n) := univ.filter fun q : PauliIndex n => ¬ sympForm G (herm q) = 0
    with hA
  have hmemA : ∀ q : PauliIndex n, q ∈ A ↔ sympForm G (herm q) = 1 := by
    intro q
    rw [hA, Finset.mem_filter]
    refine ⟨fun hq => ?_, fun h => ⟨Finset.mem_univ _, by rw [h]; decide⟩⟩
    rcases sympForm_eq_zero_or_one G (herm q) with h | h
    · exact absurd h hq.2
    · exact h
  have hpartA : ∀ q ∈ A, partner G q ∈ A := fun q hq =>
    (hmemA _).2 (by rw [sympForm_herm_partner]; exact (hmemA q).1 hq)
  -- the cross term, antisymmetric under the pairing
  set T : PauliIndex n → ℂ := fun q => partnerSign G q *
    (y.ofLp q * (starRingEnd ℂ) (y.ofLp (partner G q))
      + y.ofLp (partner G q) * (starRingEnd ℂ) (y.ofLp q)) with hT
  have hTanti : ∀ q ∈ A, T q + T (partner G q) = 0 := by
    intro q hq
    rw [hT]
    simp only
    rw [partner_partner, partnerSign_partner hG ((hmemA q).1 hq)]
    ring
  have hTsum : ∑ q ∈ A, T q = 0 :=
    Finset.sum_involution (fun q _ => partner G q) hTanti
      (fun q hq hne => by
        intro hfix
        refine hne ?_
        have := hTanti q hq
        rw [hfix] at this
        linear_combination this / 2)
      hpartA (fun q _ => partner_partner G q)
  -- and the two diagonal sums agree
  have hdiag : ∑ q ∈ A, y.ofLp (partner G q) * (starRingEnd ℂ) (y.ofLp (partner G q))
      = ∑ q ∈ A, y.ofLp q * (starRingEnd ℂ) (y.ofLp q) :=
    Finset.sum_nbij' (partner G) (partner G) hpartA hpartA (fun q _ => partner_partner G q)
      (fun q _ => partner_partner G q) (fun q _ => rfl)
  have hcast : ((∑ q ∈ A, ‖(rotAct G θ y).ofLp q‖ ^ 2 : ℝ) : ℂ)
      = ((∑ q ∈ A, ‖y.ofLp q‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    have hterm : ∀ q ∈ A, ((‖(rotAct G θ y).ofLp q‖ : ℝ) : ℂ) ^ 2
        = (Real.cos θ : ℂ) ^ 2 * (y.ofLp q * (starRingEnd ℂ) (y.ofLp q))
          + (Real.sin θ : ℂ) ^ 2
              * (y.ofLp (partner G q) * (starRingEnd ℂ) (y.ofLp (partner G q)))
          - (Real.cos θ : ℂ) * (Real.sin θ : ℂ) * T q := by
      intro q hq
      have hq1 : sympForm G (herm q) = 1 := (hmemA q).1 hq
      rw [← Complex.mul_conj', rotAct_apply, ite_eq_right (by rw [hq1]; decide)]
      rw [map_sub, map_mul, map_mul, map_mul, conj_partnerSign hG hq1]
      simp only [Complex.conj_ofReal]
      have hsign : partnerSign G q * partnerSign G q = 1 := partnerSign_mul_self hG hq1
      rw [hT]
      simp only
      linear_combination (Real.sin θ : ℂ) ^ 2
        * (y.ofLp (partner G q) * (starRingEnd ℂ) (y.ofLp (partner G q))) * hsign
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hdiag, hTsum, mul_zero, sub_zero,
      ← add_mul]
    have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
        add_comm (Real.cos θ ^ 2), Real.sin_sq_add_cos_sq, Complex.ofReal_one]
    rw [hcs, one_mul]
    exact Finset.sum_congr rfl fun q _ => Complex.mul_conj' _
  exact_mod_cast hcast

/-- **Conjugation is orthogonal on coefficient vectors**: `rotAct G θ` preserves the `ℓ²` norm,
for every Hermitian Pauli string `G` and every angle `θ`. -/
theorem norm_rotAct (hG : IsSelfAdjoint G) (θ : ℝ) (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖rotAct G θ y‖ = ‖y‖ := by
  classical
  have hsq : ‖rotAct G θ y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← Finset.sum_filter_add_sum_filter_not univ
        (fun q : PauliIndex n => sympForm G (herm q) = 0)
        (fun q => ‖(rotAct G θ y).ofLp q‖ ^ 2),
      ← Finset.sum_filter_add_sum_filter_not univ
        (fun q : PauliIndex n => sympForm G (herm q) = 0) (fun q => ‖y.ofLp q‖ ^ 2)]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun q hq => ?_) (sum_anti_norm_sq hG θ y)
    rw [rotAct_apply, ite_eq_left (Finset.mem_filter.1 hq).2]
  have h1 : (0 : ℝ) ≤ ‖rotAct G θ y‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
  nlinarith

/-! ### The inflow bound -/

/-- **The inflow into the high-weight region**. The only classes `A` maps
into `R` from outside it are partners of high-weight anticommuting classes, each with entry
`±sin(θ)`; `T` is any set of classes containing those partners. -/
lemma norm_restr_high_rotAct_low (hG : IsSelfAdjoint G) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) (T : Finset (PauliIndex n))
    (hT : ∀ q : PauliIndex n, w < wt q → sympForm G (herm q) = 1 → partner G q ∈ T) :
    ‖restr (highSet n w) (rotAct G θ (restr (highSet n w)ᶜ y))‖
      ≤ |Real.sin θ| * ‖restr T y‖ := by
  classical
  set u : EuclideanSpace ℂ (PauliIndex n) := restr (highSet n w)ᶜ y with hu
  set S : Finset (PauliIndex n) :=
    (highSet n w).filter fun q => sympForm G (herm q) = 1 with hS
  have hzero : ∀ q ∈ highSet n w, u.ofLp q = 0 := by
    intro q hq
    rw [hu, restr_apply, ite_eq_right (by simp [Finset.mem_compl, hq])]
  have hule : ∀ q : PauliIndex n, ‖u.ofLp q‖ ≤ ‖y.ofLp q‖ := by
    intro q
    rw [hu, restr_apply]
    split
    · exact le_rfl
    · simp
  have hcollapse : ∑ q ∈ S, ‖(rotAct G θ u).ofLp q‖ ^ 2
      = ∑ q ∈ highSet n w, ‖(rotAct G θ u).ofLp q‖ ^ 2 := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun q hq hqS => ?_
    have h0 : sympForm G (herm q) = 0 := by
      rcases sympForm_eq_zero_or_one G (herm q) with h | h
      · exact h
      · exact absurd (Finset.mem_filter.2 ⟨hq, h⟩) hqS
    rw [rotAct_apply, ite_eq_left h0, hzero q hq, norm_zero]
    norm_num
  have hbound : ∀ q ∈ S,
      ‖(rotAct G θ u).ofLp q‖ ^ 2 ≤ Real.sin θ ^ 2 * ‖y.ofLp (partner G q)‖ ^ 2 := by
    intro q hq
    obtain ⟨hqh, hq1⟩ := Finset.mem_filter.1 hq
    rw [rotAct_apply, ite_eq_right (by rw [hq1]; decide), hzero q hqh, mul_zero, zero_sub,
      norm_neg, norm_mul, norm_mul, norm_partnerSign hG hq1, one_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hule _) 2) (by positivity)
  have hinj : Set.InjOn (partner G) (S : Set (PauliIndex n)) :=
    fun a _ b _ hab => partner_injective G hab
  have himg : Finset.image (partner G) S ⊆ T := by
    intro t ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨hqh, hq1⟩ := Finset.mem_filter.1 hq
    exact hT q (mem_highSet.1 hqh) hq1
  have hsq : ‖restr (highSet n w) (rotAct G θ u)‖ ^ 2
      ≤ (|Real.sin θ| * ‖restr T y‖) ^ 2 := by
    rw [norm_restr_sq, ← hcollapse, mul_pow, sq_abs, norm_restr_sq, Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum hbound) ?_
    exact Finset.sum_le_sum_of_injOn (partner G) hinj himg
      (fun q _ => le_rfl) (fun t _ _ => by positivity)
  exact le_of_sq_le_sq' (norm_nonneg _) (by positivity) hsq

/-! ### The damped local norm flow -/

/-- **One rotation, with a general target set.** The high-weight norm above `w` grows by at most
`|sin θ|` times the `ℓ²` mass on any set `T` of classes that contains the partner of every
anticommuting class of weight above `w`. This is the shape of `apd:thm:local_flow_k_local`; the
choice of `T` is where the weight bound `|i G s| ≥ |s| - (k_h-1)` on the partner enters, in
`highNorm_conj_le_highNorm`. -/
theorem highNorm_conj_le (hG : IsSelfAdjoint G) (θ : ℝ) (O : Matrix (Bits n) (Bits n) ℂ)
    (T : Finset (PauliIndex n))
    (hT : ∀ q : PauliIndex n, w < wt q → sympForm G (herm q) = 1 → partner G q ∈ T) :
    highNorm w (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ))
      ≤ highNorm w O + |Real.sin θ| * ‖restr T (coeffVec O)‖ := by
  classical
  set x : EuclideanSpace ℂ (PauliIndex n) := coeffVec O with hx
  set R : Finset (PauliIndex n) := highSet n w with hR
  have hsplit : restr R (rotAct G θ x)
      = restr R (rotAct G θ (restr R x)) + restr R (rotAct G θ (restr Rᶜ x)) := by
    rw [← restr_add, ← rotAct_add, restr_add_restr_compl]
  calc highNorm w (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ))
      = ‖restr R (rotAct G θ x)‖ := by rw [highNorm, coeffVec_conj hG]
    _ ≤ ‖restr R (rotAct G θ (restr R x))‖ + ‖restr R (rotAct G θ (restr Rᶜ x))‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ ‖restr R x‖ + |Real.sin θ| * ‖restr T x‖ := by
        refine add_le_add ?_ (norm_restr_high_rotAct_low hG θ x T hT)
        calc ‖restr R (rotAct G θ (restr R x))‖ ≤ ‖rotAct G θ (restr R x)‖ := norm_restr_le _ _
          _ = ‖restr R x‖ := norm_rotAct hG _ _
    _ = highNorm w O + |Real.sin θ| * ‖restr T x‖ := rfl

/-- **`apd:thm:local_flow_k_local` for one rotation**, at a pair of thresholds
`w' + (k_h - 1) ≤ w`. Consecutive rung weights satisfy this with equality,
`w_m - (k_h-1) = w_{m-1}` (`rungWeight_add_two`). -/
theorem highNorm_conj_le_highNorm (hG : IsSelfAdjoint G) (hk : weight G ≤ kh)
    (hw : w' + (kh - 1) ≤ w) (θ : ℝ) (O : Matrix (Bits n) (Bits n) ℂ) :
    highNorm w (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ))
      ≤ highNorm w O + |Real.sin θ| * highNorm w' O := by
  refine highNorm_conj_le hG θ O (highSet n w') fun q hq h => ?_
  have h1 : wt q ≤ wt (partner G q) + (kh - 1) := by
    rw [wt_partner]
    exact weight_le_weight_mul_add_kh hk h
  exact mem_highSet.2 (by omega)

/-- The same bound with the total mass on the right — the form the ladder needs at rung `1`, where
`w_0` is the reservoir rather than a weight (see `Ladder/Defs.lean`). -/
theorem highNorm_conj_le_pauliNorm (hG : IsSelfAdjoint G) (θ : ℝ)
    (O : Matrix (Bits n) (Bits n) ℂ) :
    highNorm w (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ))
      ≤ highNorm w O + |Real.sin θ| * pauliNorm O := by
  refine le_trans (highNorm_conj_le hG θ O univ fun q _ _ => Finset.mem_univ _) ?_
  rw [restr_univ, norm_coeffVec]

/-- **Unitary invariance of the Pauli 2-norm** under conjugation by one rotation, which is what
the ladder's `reservoir` field rests on (the base case of `apd:cor:norm_cumulation_jump`). Proved
from Parseval and orthogonality of `A`, not from a separate Hilbert–Schmidt argument. -/
theorem pauliNorm_conj (hG : IsSelfAdjoint G) (θ : ℝ) (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ)) = pauliNorm O := by
  rw [← norm_coeffVec, ← norm_coeffVec, coeffVec_conj hG, norm_rotAct hG]

/-- Truncation only decreases the high-weight norms: restricting a coefficient vector to any set
of classes cannot increase its mass above any threshold. -/
theorem highNorm_restr_le (S : Finset (PauliIndex n)) (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖restr (highSet n w) (restr S y)‖ ≤ ‖restr (highSet n w) y‖ := by
  have hsq : ‖restr (highSet n w) (restr S y)‖ ^ 2 ≤ ‖restr (highSet n w) y‖ ^ 2 := by
    rw [norm_restr_sq, norm_restr_sq]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [restr_apply]
    split
    · exact le_rfl
    · simp
  exact le_of_sq_le_sq' (norm_nonneg _) (norm_nonneg _) hsq

/-- The rung spacing is exactly `k_h − 1`, which is what makes
`highNorm_conj_le_highNorm`'s hypothesis an equality at consecutive rungs. Stated from rung `1`
upwards, where `rungWeight`'s truncated subtraction is the intended value. -/
lemma rungWeight_add_two (ko kh m : ℕ) :
    rungWeight ko kh (m + 2) = rungWeight ko kh (m + 1) + (kh - 1) := by
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 1 - 1 = m := by omega
  rw [rungWeight, rungWeight, h1, h2, add_mul, one_mul, add_assoc]

/-! ### The trajectory, and the `Ladder` instance -/

/-- The evolved observable `O^{(g)} = U_g† O U_g` of `apd:thm:local_flow_k_local`, where `U_g` is
the product of the first `g` rotations `e^{-i G_l θ_l/2}`. In `Rotation.lean`'s angle convention
`rot G θ` is the `+` exponential `e^{+i G θ/2}`, so one step of the Heisenberg evolution is
`O ↦ rot G θ * O * rot G (-θ)` and the conjugation angle is `θ`. -/
noncomputable def traj (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (O : Matrix (Bits n) (Bits n) ℂ) : ℕ → Matrix (Bits n) (Bits n) ℂ
  | 0 => O
  | g + 1 => rot (toMatrix (Gs g)) (θ g) * traj Gs θ O g * rot (toMatrix (Gs g)) (-(θ g))

@[simp] lemma traj_zero (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (O : Matrix (Bits n) (Bits n) ℂ) : traj Gs θ O 0 = O := rfl

lemma traj_succ (Gs : ℕ → PauliString n) (θ : ℕ → ℝ) (O : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) :
    traj Gs θ O (g + 1)
      = rot (toMatrix (Gs g)) (θ g) * traj Gs θ O g * rot (toMatrix (Gs g)) (-(θ g)) := rfl

/-- The total mass is conserved along the trajectory: `‖O^{(g)}‖_{2,normalized} =
‖O‖_{2,normalized}` for every `g`. -/
theorem pauliNorm_traj {Gs : ℕ → PauliString n} (hG : ∀ g, IsSelfAdjoint (Gs g)) (θ : ℕ → ℝ)
    (O : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) : pauliNorm (traj Gs θ O g) = pauliNorm O := by
  induction g with
  | zero => rfl
  | succ g ih => rw [traj_succ, pauliNorm_conj (hG g), ih]

/-- **The ladder family** `N m g := ‖(U_g† O U_g)_{≥ w_m + 1}‖_{2,normalized}`
(`apd:eq:def_high_weight_norm`), with rung `0` the reservoir `‖O^{(g)}‖_{2,normalized}`. -/
noncomputable def ladderN (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (O : Matrix (Bits n) (Bits n) ℂ) (ko kh : ℕ) : ℕ → ℕ → ℝ
  | 0, g => pauliNorm (traj Gs θ O g)
  | m + 1, g => highNorm (rungWeight ko kh (m + 1)) (traj Gs θ O g)

lemma ladderN_nonneg (Gs : ℕ → PauliString n) (θ : ℕ → ℝ) (O : Matrix (Bits n) (Bits n) ℂ)
    (ko kh m g : ℕ) : 0 ≤ ladderN Gs θ O ko kh m g := by
  cases m with
  | zero => exact pauliNorm_nonneg _
  | succ m => exact highNorm_nonneg _ _

/-- The ladder's `init`: a `k_o`-local observable carries no mass above any rung `m ≥ 1`, since
`w_m ≥ w_1 = k_o`. -/
lemma ladderN_init {Gs : ℕ → PauliString n} {θ : ℕ → ℝ} {O : Matrix (Bits n) (Bits n) ℂ}
    {ko kh : ℕ} (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (m : ℕ) (hm : 1 ≤ m) :
    ladderN Gs θ O ko kh m 0 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine highNorm_eq_zero _ fun p hp => hloc p (lt_of_le_of_lt ?_ hp)
  simp only [rungWeight, Nat.add_sub_cancel]
  exact Nat.le_add_right ko (m * (kh - 1))

/-- **The Pauli model inhabits `Lean4LPD.Ladder`, and `step` is a theorem.**

`apd:thm:local_flow_k_local` discharges the `step` field, so every consequence proved for an
abstract `Ladder` applies to the Pauli model.

The hypotheses are: each generator is a Hermitian Pauli of weight at most `k_h`, the initial
observable is `k_o`-local, and `a` dominates every `|sin(θ_g)|`. Locality is read through the
coefficient vector (cf. `def:support`): every class carrying a non-zero coefficient has weight at
most `k_o`. -/
noncomputable def pauliLadder {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {O : Matrix (Bits n) (Bits n) ℂ} {ko kh : ℕ} {a : ℝ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh)
    (ha : ∀ g, |Real.sin (θ g)| ≤ a)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    Ladder a (pauliNorm O) where
  N := ladderN Gs θ O ko kh
  nonneg := ladderN_nonneg Gs θ O ko kh
  reservoir g := le_of_eq (pauliNorm_traj hG θ O g)
  init := ladderN_init hloc
  step m g hm := by
    match m, hm with
    | 1, _ =>
      change highNorm (rungWeight ko kh 1) (traj Gs θ O (g + 1))
        ≤ highNorm (rungWeight ko kh 1) (traj Gs θ O g) + a * pauliNorm (traj Gs θ O g)
      rw [traj_succ]
      exact le_trans (highNorm_conj_le_pauliNorm (hG g) (θ g) (traj Gs θ O g))
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (ha g) (pauliNorm_nonneg _)))
    | (m + 2), _ =>
      change highNorm (rungWeight ko kh (m + 2)) (traj Gs θ O (g + 1))
        ≤ highNorm (rungWeight ko kh (m + 2)) (traj Gs θ O g)
          + a * highNorm (rungWeight ko kh (m + 1)) (traj Gs θ O g)
      rw [traj_succ]
      exact le_trans
        (highNorm_conj_le_highNorm (w := rungWeight ko kh (m + 2))
          (w' := rungWeight ko kh (m + 1)) (hG g) (hk g)
          (rungWeight_add_two ko kh m).ge (θ g) (traj Gs θ O g))
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (ha g) (highNorm_nonneg _ _)))

/-- **The same family inhabits `Lean4LPD.WeightedLadder`.**

`WeightedLadder`'s fields are `Ladder`'s with the constant `a` of `step` replaced by a
rung-dependent `c m`, so the Pauli model supplies it for any `c` dominating every `|sin(θ_g)|`.
Note that the flow bound itself is **not** rung-dependent — `apd:thm:local_flow_k_local` carries
the same `sin(dt)` at every rung — so a constant `c` is the natural instance here. The rung
dependence `Ladder/Weighted.lean` exploits enters later, from the per-layer factors
`w_{j+1} sin(dt)` of `apd:cor:norm_cumulation_jump` (which come from `apd:thm:layer_inflow`), not
from this lemma. What this discharges is applicability: every theorem stated over
`WeightedLadder` has a Pauli instance. -/
noncomputable def pauliWeightedLadder {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {O : Matrix (Bits n) (Bits n) ℂ} {ko kh : ℕ} {c : ℕ → ℝ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh)
    (hc : ∀ g m, |Real.sin (θ g)| ≤ c m)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    WeightedLadder c (pauliNorm O) where
  N := ladderN Gs θ O ko kh
  nonneg := ladderN_nonneg Gs θ O ko kh
  reservoir g := le_of_eq (pauliNorm_traj hG θ O g)
  init := ladderN_init hloc
  step m g hm := by
    match m, hm with
    | 1, _ =>
      change highNorm (rungWeight ko kh 1) (traj Gs θ O (g + 1))
        ≤ highNorm (rungWeight ko kh 1) (traj Gs θ O g) + c 1 * pauliNorm (traj Gs θ O g)
      rw [traj_succ]
      exact le_trans (highNorm_conj_le_pauliNorm (hG g) (θ g) (traj Gs θ O g))
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hc g 1) (pauliNorm_nonneg _)))
    | (m + 2), _ =>
      change highNorm (rungWeight ko kh (m + 2)) (traj Gs θ O (g + 1))
        ≤ highNorm (rungWeight ko kh (m + 2)) (traj Gs θ O g)
          + c (m + 2) * highNorm (rungWeight ko kh (m + 1)) (traj Gs θ O g)
      rw [traj_succ]
      exact le_trans
        (highNorm_conj_le_highNorm (w := rungWeight ko kh (m + 2))
          (w' := rungWeight ko kh (m + 1)) (hG g) (hk g)
          (rungWeight_add_two ko kh m).ge (θ g) (traj Gs θ O g))
        (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (hc g (m + 2)) (highNorm_nonneg _ _)))

/-- **A single Pauli observable inhabits the ladder**, so `pauliLadder`'s hypotheses are not
satisfiable only in principle. Locality is `coeff_toMatrix_herm_eq_zero`: a basis Pauli's
coefficient vector is a unit vector, hence carries nothing above weight `|q|`. -/
noncomputable def pauliLadderOfHerm {Gs : ℕ → PauliString n} {θ : ℕ → ℝ} {kh : ℕ} {a : ℝ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh)
    (ha : ∀ g, |Real.sin (θ g)| ≤ a) (q : PauliIndex n) :
    Ladder a (pauliNorm (toMatrix (herm q))) :=
  pauliLadder (ko := wt q) hG hk ha fun _ hp => coeff_toMatrix_herm_eq_zero hp

/-- Fully concrete, so that nothing above is inhabited only in principle: one qubit, every
generator `X`, observable `Z`, conjugation angle `dt`. `X` and `Z` anticommute
(`sympForm_X1_Z1`), so the branch that actually moves mass is live rather than empty. -/
noncomputable example (dt : ℝ) : Ladder |Real.sin dt| (pauliNorm (toMatrix Z1)) := by
  have hz : herm (cls Z1) = Z1 := by decide
  refine hz ▸ pauliLadderOfHerm (Gs := fun _ => X1) (θ := fun _ => dt) (kh := 1)
    (fun _ => isSelfAdjoint_X1) (fun _ => ?_) (fun _ => le_rfl) (cls Z1)
  decide

/-- **`apd:thm:local_flow_k_local`, in the paper's variables.**

For a Hermitian `k_h`-local generator and a rung `m ≥ 2`, the high-weight norm above
`w_m = k_o + (m-1)(k_h-1)` grows by at most `|sin(dt)|` times the norm above
`w_{m-1}`. Rung `1` needs `highNorm_conj_le_pauliNorm` instead, which bounds the inflow by the
total mass; rung `0` is the reservoir, not a weight.

The inequality holds for every operator `O` and every angle `θ`: no locality hypothesis on the
observable is used, which is stronger than the paper's statement. Here `k_o` only fixes the
rung weights. -/
theorem local_flow_k_local {ko m : ℕ} (hG : IsSelfAdjoint G) (hk : weight G ≤ kh) (hm : 2 ≤ m)
    (θ : ℝ) (O : Matrix (Bits n) (Bits n) ℂ) :
    highNorm (rungWeight ko kh m) (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ))
      ≤ highNorm (rungWeight ko kh m) O
        + |Real.sin θ| * highNorm (rungWeight ko kh (m - 1)) O := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  refine highNorm_conj_le_highNorm hG hk ?_ θ O
  rw [show k + 2 - 1 = k + 1 from by omega]
  exact (rungWeight_add_two ko kh k).ge

end PauliString

end Lean4LPD
