/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import LeanPool.MooreBound.DegreeDiameter.CommonBasis
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Exact enumeration of complete flags

For a natural number `q`, `qInteger q n` is the polynomial
`1 + q + ... + q^(n-1)`.  The product `qFactorial q n` is

`[n]_q [n-1]_q ... [1]_q`.

The order of the factors is reversed only to make the factorization used in
the proof definitionally transparent; multiplication in `ℕ` is commutative.

We prove the complete-flag formula by counting adapted ordered bases.  For a
complete flag `F`, an adapted vector at step `i` is a vector in
`F_(i+1) \ F_i`.  Choosing one at every step always gives a basis, and every
ordered basis is obtained exactly once after retaining its induced flag.
Mathlib's exact enumeration of linearly independent tuples then gives the
q-factorial formula.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

public section

namespace MooreBound

open Module
open scoped BigOperators

namespace DegreeDiameter

/-- The `q`-integer `[n]_q = 1 + q + ... + q^(n-1)`. -/
@[expose] def qInteger (q n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, q ^ i

/-- The `q`-factorial `[n]_q! = [n]_q [n-1]_q ... [1]_q`.

Writing the factors in descending order agrees with the usual q-factorial
because multiplication in `ℕ` is commutative. -/
def qFactorial (q n : ℕ) : ℕ :=
  ∏ i : Fin n, qInteger q (n - i.val)

@[simp]
theorem qInteger_zero (q : ℕ) : qInteger q 0 = 0 := by
  simp [qInteger]

@[simp]
theorem qInteger_one (q : ℕ) : qInteger q 1 = 1 := by
  simp [qInteger]

@[simp]
theorem qFactorial_zero (q : ℕ) : qFactorial q 0 = 1 := by
  simp [qFactorial]

theorem qFactorial_succ (q n : ℕ) :
    qFactorial q (n + 1) = qInteger q (n + 1) * qFactorial q n := by
  rw [qFactorial, Fin.prod_univ_succ, qFactorial]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  simp

/-- The descending-product definition is the conventional ascending product
`[1]_q [2]_q ... [n]_q`. -/
theorem qFactorial_eq_prod_range (q n : ℕ) :
    qFactorial q n = ∏ j ∈ Finset.range n, qInteger q (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [qFactorial_succ, Finset.prod_range_succ, ih, Nat.mul_comm]

theorem qInteger_mul_sub_one (q n : ℕ) (hq : 1 ≤ q) :
    qInteger q n * (q - 1) = q ^ n - 1 := by
  simpa [qInteger] using (geom_sum_mul_of_one_le hq n)

section CompleteFlagFinite

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  {n : ℕ}

/-- Complete flags form a finite type when the ambient vector space is
finite. -/
noncomputable instance CompleteFlag.instFinite [Finite V] :
    Finite (CompleteFlag K V n) := by
  let : Finite (Submodule K V) :=
    Finite.of_injective (fun S : Submodule K V ↦ (S : Set V)) SetLike.coe_injective
  exact Finite.of_injective
    (fun F : CompleteFlag K V n ↦ F.space)
    (fun _ _ h ↦ CompleteFlag.ext (congrFun h))

end CompleteFlagFinite

section AdaptedBases

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : ℕ}

/-- A vector which advances the complete flag `F` from rank `i` to rank
`i+1`. -/
def FlagStepVector (F : CompleteFlag K V n) (i : Fin n) :=
  {x : F i.succ // (x : V) ∉ F i.castSucc}

noncomputable instance flagStepVectorFinite [Finite V]
    (F : CompleteFlag K V n) (i : Fin n) : Finite (FlagStepVector F i) := by
  unfold FlagStepVector
  infer_instance

/-- One advancing vector at every rank of a complete flag. -/
def FlagStepChoices (F : CompleteFlag K V n) :=
  (i : Fin n) → FlagStepVector F i

noncomputable instance flagStepChoicesFinite [Finite V]
    (F : CompleteFlag K V n) : Finite (FlagStepChoices F) := by
  unfold FlagStepChoices
  infer_instance

/-- A complete flag together with a choice of one advancing vector at every
rank. -/
@[expose]
def AdaptedFlagBasis (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (n : ℕ) :=
  Σ F : CompleteFlag K V n, FlagStepChoices F

/-- Forget the submodule-membership proofs in an adapted flag basis. -/
def adaptedVectors (d : AdaptedFlagBasis K V n) : Fin n → V :=
  fun i ↦ ((d.2 i).1 : V)

/-- Vectors in the preceding subspace, regarded as vectors in the next
subspace. -/
def previousStepEquiv (F : CompleteFlag K V n) (i : Fin n) :
    {x : F i.succ // (x : V) ∈ F i.castSucc} ≃ F i.castSucc where
  toFun x := ⟨x.1, x.2⟩
  invFun x :=
    ⟨⟨x.1, F.strictMono_space.monotone Fin.castSucc_lt_succ.le x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem natCard_flagStepVector [Finite K] [Finite V]
    (F : CompleteFlag K V n) (i : Fin n) :
    Nat.card (FlagStepVector F i) =
      Nat.card K ^ (i.val + 1) - Nat.card K ^ i.val := by
  classical
  let := Fintype.ofFinite K
  let := Fintype.ofFinite (F i.succ)
  let := Fintype.ofFinite (F i.castSucc)
  let := Fintype.ofFinite
    {x : F i.succ // (x : V) ∈ F i.castSucc}
  let := Fintype.ofFinite (FlagStepVector F i)
  change Nat.card {x : F i.succ // ¬((x : V) ∈ F i.castSucc)} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  rw [Nat.card_congr (previousStepEquiv F i)]
  rw [Module.natCard_eq_pow_finrank (K := K) (V := F i.succ)]
  rw [Module.natCard_eq_pow_finrank (K := K) (V := F i.castSucc)]
  rw [F.finrank_space, F.finrank_space]
  rfl

theorem adaptedVectors_linearIndependent (d : AdaptedFlagBasis K V n) :
    LinearIndependent K (adaptedVectors d) := by
  let v := adaptedVectors d
  let F := d.1
  have hv_mem (i : Fin n) : v i ∈ F i.succ := (d.2 i).1.2
  have hv_not (i : Fin n) : v i ∉ F i.castSucc := (d.2 i).2
  let vr : (r : ℕ) → r ≤ n → Fin r → V := fun r hr i ↦
    v ⟨i.val, i.isLt.trans_le hr⟩
  have hLIprefix : ∀ (r : ℕ) (hr : r ≤ n), LinearIndependent K (vr r hr) := by
    intro r
    induction r with
    | zero =>
        intro _
        exact linearIndependent_empty_type
    | succ r ih =>
        intro hr
        rw [linearIndependent_finSucc']
        constructor
        · have heq : Fin.init (vr (r + 1) hr) = vr r (Nat.le_of_succ_le hr) := by
            funext i
            rfl
          rw [heq]
          exact ih (Nat.le_of_succ_le hr)
        · intro hmem
          have hspan_le :
              Submodule.span K (Set.range (Fin.init (vr (r + 1) hr))) ≤
                F ⟨r, by omega⟩ := by
            rw [Submodule.span_le]
            intro x hx
            obtain ⟨i, rfl⟩ := hx
            have hvi := hv_mem ⟨i.val, by omega⟩
            exact F.strictMono_space.monotone
              (Fin.castSucc_lt_iff_succ_le.mp (show i.val < r from i.isLt)) hvi
          exact hv_not ⟨r, by omega⟩ (hspan_le hmem)
  simpa [v, vr] using hLIprefix n le_rfl

/-- The span of the first `r` adapted vectors is exactly the rank-`r`
subspace of the flag. -/
theorem span_adaptedVectors_eq (d : AdaptedFlagBasis K V n)
    [FiniteDimensional K V]
    (r : Fin (n + 1)) :
    Submodule.span K
        (adaptedVectors d '' {i : Fin n | i.castSucc < r}) = d.1 r := by
  classical
  have hLI : LinearIndependent K (adaptedVectors d) :=
    adaptedVectors_linearIndependent d
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact d.1.strictMono_space.monotone
      (Fin.castSucc_lt_iff_succ_le.mp hi) (d.2 i).1.2
  · calc
      finrank K (Submodule.span K
          (adaptedVectors d '' {i : Fin n | i.castSucc < r})) = r.val := by
            rw [finrank_span_set_eq_card
              ((hLI.linearIndepOn _).id_image)]
            rw [Set.toFinset_image,
              Finset.card_image_of_injective _ hLI.injective]
            rw [Set.toFinset_ofPred]
            change
              (Finset.filter (fun x : Fin n ↦ x.val < r.val) Finset.univ).card =
                r.val
            rw [Fin.card_filter_val_lt,
              Nat.min_eq_right (Nat.le_of_lt_succ r.isLt)]
      _ = finrank K (d.1 r) := (d.1.finrank_space r).symm

/-- An adapted flag basis is exactly a linearly independent `n`-tuple. -/
noncomputable def adaptedFlagBasisEquivLinearIndependent
    [FiniteDimensional K V] (hV : finrank K V = n) :
    AdaptedFlagBasis K V n ≃
      {v : Fin n → V // LinearIndependent K v} := by
  let f : AdaptedFlagBasis K V n →
      {v : Fin n → V // LinearIndependent K v} := fun d ↦
    ⟨adaptedVectors d, adaptedVectors_linearIndependent d⟩
  apply Equiv.ofBijective f
  constructor
  · intro d e h
    have hv : adaptedVectors d = adaptedVectors e :=
      congrArg Subtype.val h
    have hflag : d.1 = e.1 := by
      apply CompleteFlag.ext
      intro r
      rw [← span_adaptedVectors_eq d r, ← span_adaptedVectors_eq e r, hv]
    cases d with
    | mk F a =>
      cases e with
      | mk G b =>
        dsimp only at hflag ⊢
        subst G
        have hab : a = b := by
          funext i
          apply Subtype.ext
          apply Subtype.ext
          exact congrFun hv i
        subst b
        rfl
  · intro s
    let b : Basis (Fin n) K V :=
      basisOfLinearIndependentOfCardEqFinrank' s.1 s.2 (by
        simp [hV])
    have hb : (b : Fin n → V) = s.1 :=
      coe_basisOfLinearIndependentOfCardEqFinrank' s.1 s.2 (by
        simp [hV])
    let F : CompleteFlag K V n := CompleteFlag.ofBasis b
    let a : FlagStepChoices F := fun i ↦
      ⟨⟨b i, by
        simpa only [F, CompleteFlag.ofBasis_space] using
          b.self_mem_flag (i := i) (k := i.succ) (by simp)⟩, by
        intro hmem
        have hmem' : b i ∈ b.flag i.castSucc := by
          simpa only [F, CompleteFlag.ofBasis_space] using hmem
        exact (lt_irrefl i.castSucc) ((b.self_mem_flag_iff).mp hmem')⟩
    refine ⟨⟨F, a⟩, ?_⟩
    apply Subtype.ext
    funext i
    change b i = s.1 i
    exact congrFun hb i

end AdaptedBases

section Arithmetic

/-- The factor in the exact count of independent tuples splits into the
number of choices advancing a fixed flag and the corresponding q-integer. -/
theorem independentFactor_eq (q n : ℕ) (hq : 1 ≤ q) (i : Fin n) :
    q ^ n - q ^ i.val =
      (q ^ (i.val + 1) - q ^ i.val) * qInteger q (n - i.val) := by
  have hi : i.val ≤ n := Nat.le_of_lt i.isLt
  have hn : i.val + (n - i.val) = n := Nat.add_sub_of_le hi
  have hgeom := qInteger_mul_sub_one q (n - i.val) hq
  have hadvance :
      q ^ (i.val + 1) - q ^ i.val = q ^ i.val * (q - 1) := by
    rw [pow_succ]
    simpa using (Nat.mul_sub_left_distrib (q ^ i.val) q 1).symm
  calc
    q ^ n - q ^ i.val =
        q ^ i.val * q ^ (n - i.val) - q ^ i.val * 1 := by
          rw [← pow_add, hn, mul_one]
    _ = q ^ i.val * (q ^ (n - i.val) - 1) := by
          rw [Nat.mul_sub_left_distrib]
    _ = q ^ i.val * (qInteger q (n - i.val) * (q - 1)) := by
          rw [hgeom]
    _ = (q ^ i.val * (q - 1)) * qInteger q (n - i.val) := by
          ac_rfl
    _ = (q ^ (i.val + 1) - q ^ i.val) * qInteger q (n - i.val) := by
          rw [hadvance]

theorem independentProduct_eq (q n : ℕ) (hq : 1 ≤ q) :
    (∏ i : Fin n, (q ^ n - q ^ i.val)) =
      (∏ i : Fin n, (q ^ (i.val + 1) - q ^ i.val)) * qFactorial q n := by
  rw [qFactorial]
  calc
    (∏ i : Fin n, (q ^ n - q ^ i.val)) =
        ∏ i : Fin n,
          ((q ^ (i.val + 1) - q ^ i.val) * qInteger q (n - i.val)) := by
            apply Finset.prod_congr rfl
            intro i _
            exact independentFactor_eq q n hq i
    _ = (∏ i : Fin n, (q ^ (i.val + 1) - q ^ i.val)) *
          ∏ i : Fin n, qInteger q (n - i.val) := by
            exact Finset.prod_mul_distrib

end Arithmetic

section CompleteFlagCount

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [Finite V] [FiniteDimensional K V]

/-- The exact number of complete flags in an `n`-dimensional vector space
over a finite field is `[n]_q!`, where `q` is the cardinality of the field. -/
theorem natCard_completeFlag_of_finrank {n : ℕ}
    (hV : finrank K V = n) :
    Nat.card (CompleteFlag K V n) = qFactorial (Nat.card K) n := by
  classical
  let := Fintype.ofFinite K
  let := Fintype.ofFinite V
  let := Fintype.ofFinite (CompleteFlag K V n)
  let q := Nat.card K
  let A := ∏ i : Fin n, (q ^ (i.val + 1) - q ^ i.val)
  have hq : 1 < q := by
    simpa [q, Nat.card_eq_fintype_card] using (Fintype.one_lt_card : 1 < Fintype.card K)
  have hA : 0 < A := by
    apply Finset.prod_pos
    intro i _
    rw [Nat.sub_pos_iff_lt]
    exact pow_lt_pow_right₀ hq (Nat.lt_succ_self i.val)
  have hdata :
      Nat.card (AdaptedFlagBasis K V n) =
        Nat.card (CompleteFlag K V n) * A := by
    change Nat.card (Σ F : CompleteFlag K V n, FlagStepChoices F) = _
    rw [Nat.card_sigma]
    simp_rw [FlagStepChoices, Nat.card_pi, natCard_flagStepVector]
    simp [A, q, Nat.card_eq_fintype_card]
  have hindependent :
      Nat.card {v : Fin n → V // LinearIndependent K v} =
        ∏ i : Fin n, (q ^ n - q ^ i.val) := by
    have h := card_linearIndependent (K := K) (V := V) (k := n) (by rw [hV])
    simpa [q, hV, Nat.card_eq_fintype_card] using h
  have hcount :
      Nat.card (CompleteFlag K V n) * A =
        ∏ i : Fin n, (q ^ n - q ^ i.val) := by
    rw [← hdata]
    rw [Nat.card_congr
      (adaptedFlagBasisEquivLinearIndependent (K := K) (V := V) (n := n) hV)]
    exact hindependent
  have hfactor :
      (∏ i : Fin n, (q ^ n - q ^ i.val)) = A * qFactorial q n :=
    independentProduct_eq q n hq.le
  apply Nat.eq_of_mul_eq_mul_right hA
  calc
    Nat.card (CompleteFlag K V n) * A =
        ∏ i : Fin n, (q ^ n - q ^ i.val) := hcount
    _ = A * qFactorial q n := hfactor
    _ = qFactorial q n * A := Nat.mul_comm _ _

/-- Coordinate-space specialization of `natCard_completeFlag_of_finrank`.
This is the literal formula `|Flag(K^n)| = [n]_(|K|)!`. -/
theorem natCard_completeFlag_finFun (n : ℕ) :
    Nat.card (CompleteFlag K (Fin n → K) n) =
      qFactorial (Nat.card K) n := by
  apply natCard_completeFlag_of_finrank
  simp

end CompleteFlagCount

end DegreeDiameter

end MooreBound
