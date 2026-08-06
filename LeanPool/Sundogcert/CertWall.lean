/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.Certificate
import LeanPool.Sundogcert.Looseness

/-!
  Sundogcert/CertWall.lean — TYPING the imported hardness wall as a CONDITIONAL theorem.

  The prose the certificate ships with says:

    "a cheap, basis-robust, TIGHT reject bound would be a fast decoder, so the
     basis-dependence of `colWeightLb` is the visible edge of the imported hardness."

  This module turns that PROSE into TYPED Lean.  It does NOT prove decoding hardness,
  P≠NP, or one-wayness — those stay an IMPORTED assumption (ISD/SIS), named honestly.
  What is proved here is the WALL's SHAPE:

    (1) `minCosetWeight H z` = the true semantic quantity the verifier lower-bounds: the
        minimum Hamming weight over the syndrome coset `{ e' | H e' = z }`.  Computing it
        WITH a witness IS decoding (the imported-hard FIND problem); the verifier only ever
        holds a cheap SOUND lower bound on it.

    (2) CODE-INVARIANCE (`minCosetWeight_rowEquiv`): `minCosetWeight` depends only on the
        CODE (`ker H`), not the BASIS `H`.  Left-multiplying `H` by an invertible `M` (a
        row-operation / change of parity-check basis) leaves `minCosetWeight` unchanged on
        corresponding syndromes.  REAL content — a genuine coset bijection.

    (3) BASIS-DEPENDENCE of `colWeightLb` (`colWeightLb_not_basis_invariant`): the cheap sound
        bound is NOT a code invariant.  On the dense row-equivalent `H` of the SAME code it
        collapses to `0` while the true `minCosetWeight` stays `≥ m`.  Instantiates Looseness's
        `looseness`/`safe_dense_iff_proj` (a concrete, witnessed counterexample).

    (4) THE TYPED WALL (`tight_bound_decodes`, CONDITIONAL): IF a verifier's bound `lb` is tight
        on a body's syndrome (`lb z = minCosetWeight z`) THEN evaluating that cheap bound there
        COMPUTES the decoding distance.  HONEST: the antecedent "tight on this code" IS the
        decoding answer — the theorem TYPES that equivalence, it does NOT discharge it.  With
        (2)+(3): a bound tight on EVERY basis would be a code invariant (2), yet `colWeightLb`
        provably is not (3); so "cheap + basis-robust + tight" is exactly the imported-hard
        decoder, which `colWeightLb` (and the cheap bounds here) do NOT achieve.

  HONESTY LEDGER.  (1) is definitional ground truth.  (2) is a non-trivial invariance (the
  invertible-`M` coset bijection).  (3) is a concrete refutation with witnessed schemes
  (`projScheme` vs `denseScheme`).  (4) is deliberately a CONDITIONAL whose hypothesis IS the
  decoding assumption, so it makes NO unconditional hardness claim.  The synthesis
  (`colWeightLb_cannot_be_tight_basisRobust`) is a CONSEQUENCE of (2)+(3) stated about
  `colWeightLb` only — never a claim about the hardness of decoding itself.
-/

open Matrix

namespace Sundog.Certificate.CertWall

open Sundog.Certificate
open Sundog.Certificate.Scaling
open Sundog.Certificate.Looseness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### (1) The true semantic quantity: minimum coset weight (over an explicit `H`). -/

/-- **Minimum coset weight** of a syndrome `z` under parity-check `H` — the ground-truth
    quantity the verifier's `lb` lower-bounds.  The least Hamming weight over all error patterns
    with that syndrome.  Computing it WITH a witness IS decoding (the imported-hard FIND
    problem); the verifier only ever has a cheap SOUND lower bound on it. -/
noncomputable def minCosetWeight {m n : ℕ} (H : Matrix (Fin m) (Fin n) F)
    (z : Fin m → F) : ℕ :=
  sInf {w | ∃ e' : Fin n → F, H *ᵥ e' = z ∧ wt e' = w}

omit [Fintype F] in
/-- The witness set of a body's own syndrome is always nonempty (the body itself qualifies). -/
theorem minCosetWeight_set_nonempty {m n : ℕ} (H : Matrix (Fin m) (Fin n) F)
    (y : Fin n → F) :
    {w | ∃ e' : Fin n → F, H *ᵥ e' = H *ᵥ y ∧ wt e' = w}.Nonempty :=
  ⟨wt y, y, rfl, rfl⟩

/-- `Safe S y` is exactly "`minCosetWeight` of the body's syndrome is `≤ τ`" — the bridge that
    makes `minCosetWeight` the genuine semantic target of the verifier. -/
theorem safe_iff_minCosetWeight_le (S : Scheme F) (y : Fin S.n → F) :
    Safe S y ↔ minCosetWeight S.H (S.H *ᵥ y) ≤ S.τ := by
  unfold Safe minCosetWeight
  constructor
  · rintro ⟨e', he, hwt⟩
    exact le_trans (Nat.sInf_le ⟨e', he, rfl⟩) hwt
  · intro h
    obtain ⟨e', he, hwe⟩ := Nat.sInf_mem (minCosetWeight_set_nonempty S.H y)
    exact ⟨e', he, hwe ▸ h⟩

/-! ### (2) CODE-INVARIANCE — `minCosetWeight` depends only on the code, not the basis.

    Left-multiplying `H` by an invertible `M` is a change of parity-check basis (a row
    operation): the kernel/code is unchanged, the cosets are in bijection, so the minimum coset
    weight is unchanged on corresponding syndromes.  No cross-`Scheme` transport needed. -/

omit [Fintype F] [DecidableEq F] in
/-- The coset is preserved by a row-equivalent parity check `M * H` (`M` invertible): `e'` has
    `M*H`-syndrome `(M*H) y` iff it has `H`-syndrome `H y`. -/
theorem mulVec_eq_iff_of_invertible {m n : ℕ} (M : Matrix (Fin m) (Fin m) F) [Invertible M]
    (H : Matrix (Fin m) (Fin n) F) (e' y : Fin n → F) :
    (M * H) *ᵥ e' = (M * H) *ᵥ y ↔ H *ᵥ e' = H *ᵥ y := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    exact Matrix.mulVec_injective_of_invertible M h
  · intro h
    rw [h]

omit [Fintype F] in
/-- **CODE-INVARIANCE (the meaningful theorem).**  A change of parity-check basis (left-multiply
    `H` by an invertible `M`) leaves the minimum coset weight unchanged on the corresponding
    syndrome.  The true decoding distance is a CODE invariant — it cannot see the basis. -/
theorem minCosetWeight_rowEquiv {m n : ℕ} (M : Matrix (Fin m) (Fin m) F) [Invertible M]
    (H : Matrix (Fin m) (Fin n) F) (y : Fin n → F) :
    minCosetWeight (M * H) ((M * H) *ᵥ y) = minCosetWeight H (H *ᵥ y) := by
  unfold minCosetWeight
  congr 1
  ext w
  constructor
  · rintro ⟨e', he, hwe⟩
    exact ⟨e', (mulVec_eq_iff_of_invertible M H e' y).mp he, hwe⟩
  · rintro ⟨e', he, hwe⟩
    exact ⟨e', (mulVec_eq_iff_of_invertible M H e' y).mpr he, hwe⟩

/-! ### (3) BASIS-DEPENDENCE of `colWeightLb` — it is NOT a code invariant.

    Concrete witness from Looseness: the same code (`safe_dense_iff_proj`), same all-ones body,
    but `colWeightLb` is `m` under the sparse `projScheme` and `0` under the dense `denseScheme`
    — while the code-invariant `minCosetWeight` stays `≥ m` on both. -/

/-- `colWeightLb` on the sparse projection scheme equals the true distance `m`. -/
theorem colWeightLb_projScheme_eq (m : ℕ) (hm : 0 < m) :
    colWeightLb (projScheme m) ((projScheme m).H *ᵥ allOnesSynBody m) = m := by
  unfold colWeightLb
  change hammingNorm (projH m *ᵥ allOnesSynBody m) / colBound (projH m) = m
  rw [hammingNorm_projH_allOnes, colBound_projH m hm, Nat.div_one]

/-- The all-ones body has Hamming weight `≤ m`: its support sits inside the first `m`
    coordinates of `Fin (2*m)`, which inject into `Fin m`.  (Used to cap `minCosetWeight` from
    above — the all-ones body is a coset witness of weight `≤ m`.) -/
theorem wt_allOnesSynBody_le (m : ℕ) (hm : 0 < m) : wt (allOnesSynBody m) ≤ m := by
  rw [wt, hammingNorm]
  -- support ⊆ {j | (j:ℕ) < m}; map j ↦ ⟨j.val % m, _⟩ : Fin m injectively into univ.
  have hbound : (Finset.univ.filter (fun i : Fin (2 * m) => allOnesSynBody m i ≠ 0)).card
      ≤ (Finset.univ : Finset (Fin m)).card := by
    refine Finset.card_le_card_of_injOn
      (fun j => (⟨(j : ℕ) % m, Nat.mod_lt _ hm⟩ : Fin m)) (fun j _ => Finset.mem_univ _) ?_
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at ha hb
      -- a,b in support ⟹ nonzero ⟹ (·:ℕ) < m ⟹ %m is identity ⟹ injective.
      have ham : (a : ℕ) < m := by
        by_contra h; unfold allOnesSynBody at ha; simp [h] at ha
      have hbm : (b : ℕ) < m := by
        by_contra h; unfold allOnesSynBody at hb; simp [h] at hb
      have hval : (a : ℕ) % m = (b : ℕ) % m := congrArg Fin.val hab
      rw [Nat.mod_eq_of_lt ham, Nat.mod_eq_of_lt hbm] at hval
      exact Fin.ext hval
  rw [Finset.card_univ, Fintype.card_fin] at hbound
  exact hbound

/-- The dense scheme's all-ones body has true min coset weight `≥ m` — the SAME code is unsafe
    at `τ = m-1`, so no coset witness has weight `≤ m-1`.  (Code-invariant.) -/
theorem minCosetWeight_denseScheme_ge (m : ℕ) (hm : 2 ≤ m) :
    m ≤ minCosetWeight (denseScheme m).H ((denseScheme m).H *ᵥ allOnesSynBody m) := by
  by_contra h
  have hlt : minCosetWeight (denseScheme m).H
      ((denseScheme m).H *ᵥ allOnesSynBody m) < m := Nat.lt_of_not_le h
  -- minCosetWeight < m ⟹ ≤ m-1 = τ ⟹ Safe, contradicting looseness's ¬Safe.
  have hle : minCosetWeight (denseScheme m).H
      ((denseScheme m).H *ᵥ allOnesSynBody m) ≤ (denseScheme m).τ := by
    change minCosetWeight (denseScheme m).H
      ((denseScheme m).H *ᵥ allOnesSynBody m) ≤ m - 1
    omega
  exact (looseness m hm).1 ((safe_iff_minCosetWeight_le (denseScheme m) (allOnesSynBody m)).mpr hle)

/-- **`colWeightLb` is BASIS-DEPENDENT (the typed looseness).**  There is a code (the `[2m,m]`
    family, `m ≥ 2`) and a syndrome on which two parity-check bases of THAT code give different
    `colWeightLb` — `m` on the sparse basis, `0` on the dense one.  So `colWeightLb` is NOT a
    code invariant; it cannot be the decoding distance on every basis. -/
theorem colWeightLb_not_basis_invariant (m : ℕ) (hm : 2 ≤ m) :
    colWeightLb (projScheme m) ((projScheme m).H *ᵥ allOnesSynBody m) ≠
      colWeightLb (denseScheme m) ((denseScheme m).H *ᵥ allOnesSynBody m) := by
  rw [colWeightLb_projScheme_eq m (by omega), colWeightLb_denseScheme_zero m hm]
  omega

/-! ### (4) THE TYPED WALL — a CONDITIONAL, not a hardness proof. -/

/-- A bound `lb` is **TIGHT at `z`** for parity-check `H` when it equals the true minimum coset
    weight there.  Tightness at `z` (with a witness) IS the decoding answer for `z` — the
    imported-hard quantity. -/
def TightAt {m n : ℕ} (H : Matrix (Fin m) (Fin n) F) (lb : (Fin m → F) → ℕ)
    (z : Fin m → F) : Prop :=
  lb z = minCosetWeight H z

/-- **THE TYPED WALL (conditional).**  IF a verifier's bound is tight on a body's syndrome, THEN
    evaluating that cheap bound there EQUALS the decoding distance `minCosetWeight` — i.e. the
    cheap evaluation decides the imported-hard decoding question.  This is the HONEST typing of
    "a cheap, basis-robust, tight bound is a decoder": the conclusion is decoding, reached ONLY
    under the tightness HYPOTHESIS; nothing here discharges that hypothesis, so NO
    hardness/P≠NP/one-wayness claim is made. -/
theorem tight_bound_decodes (S : Scheme F) (V : Verifier S) (y : Fin S.n → F)
    (hTight : TightAt S.H V.lb (S.H *ᵥ y)) :
    V.lb (S.H *ᵥ y) = minCosetWeight S.H (S.H *ᵥ y) :=
  hTight

/-- **SYNTHESIS (consequence of (2)+(3), about `colWeightLb` only).**  `colWeightLb` cannot be
    tight on every basis of a code: it is tight on the sparse projection (`= m = minCosetWeight`)
    but on the dense row-equivalent basis of the SAME code it is `0 ≠ minCosetWeight` (which is
    `≥ m`).  So `colWeightLb` is NOT a basis-robust tight bound — exactly the gap the imported
    hardness lives in.  (No claim that NO cheap bound could be tight everywhere — that WOULD be a
    decoder, which stays an imported assumption.) -/
theorem colWeightLb_cannot_be_tight_basisRobust (m : ℕ) (hm : 2 ≤ m) :
    TightAt (projScheme m).H (colWeightLb (projScheme m))
        ((projScheme m).H *ᵥ allOnesSynBody m) ∧
      ¬ TightAt (denseScheme m).H (colWeightLb (denseScheme m))
        ((denseScheme m).H *ᵥ allOnesSynBody m) := by
  constructor
  · -- TIGHT on sparse: colWeightLb = m, and minCosetWeight = m too.
    unfold TightAt
    rw [colWeightLb_projScheme_eq m (by omega)]
    -- minCosetWeight (projScheme m) = m: ≤ m via the all-ones witness, ≥ m via unsafety.
    apply le_antisymm
    · -- m ≤ minCosetWeight: the SAME-code unsafety at τ=m-1 forces every witness weight ≥ m.
      by_contra h
      have hlt : minCosetWeight (projScheme m).H
          ((projScheme m).H *ᵥ allOnesSynBody m) < m := Nat.lt_of_not_le h
      have hle : minCosetWeight (projScheme m).H
          ((projScheme m).H *ᵥ allOnesSynBody m) ≤ (projScheme m).τ := by
        change minCosetWeight (projScheme m).H
          ((projScheme m).H *ᵥ allOnesSynBody m) ≤ m - 1
        omega
      exact scaling_law m (by omega)
        ((safe_iff_minCosetWeight_le (projScheme m) (allOnesSynBody m)).mpr hle)
    · -- minCosetWeight ≤ wt(allOnes) ≤ m: all-ones body is a coset witness of weight ≤ m.
      calc minCosetWeight (projScheme m).H ((projScheme m).H *ᵥ allOnesSynBody m)
          ≤ wt (allOnesSynBody m) := Nat.sInf_le ⟨allOnesSynBody m, rfl, rfl⟩
        _ ≤ m := wt_allOnesSynBody_le m (by omega)
  · -- NOT tight on dense: colWeightLb = 0 but minCosetWeight ≥ m > 0.
    unfold TightAt
    rw [colWeightLb_denseScheme_zero m hm]
    intro hcontra
    have := minCosetWeight_denseScheme_ge m hm
    omega


end Sundog.Certificate.CertWall
