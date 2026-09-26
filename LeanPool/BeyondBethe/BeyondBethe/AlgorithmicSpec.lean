/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.Completion
public import LeanPool.BeyondBethe.Complexitylib.Classes.P
public import LeanPool.BeyondBethe.Complexitylib.Encoding.DataEncode
public import LeanPool.BeyondBethe.Complexitylib.Encoding.Pairing
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Pairing

/-! # Algorithmic Spec -/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- A square rational matrix together with its dimension.  Bundling the
dimension turns the family of inputs in Theorem 1 into one machine input
type. -/
abbrev RationalMatrixInput := Σ n : ℕ, Matrix (Fin n) (Fin n) ℚ

/-- The signed-magnitude payload used for integers.  The Boolean distinguishes
`ofNat` from `negSucc`, so this representation has no duplicate zero. -/
def integerPayload : ℤ → Bool × ℕ
  | .ofNat n => (false, n)
  | .negSucc n => (true, n + 1)

theorem integerPayload_injective : Function.Injective integerPayload := by
  intro a b h
  cases a <;> cases b <;> simp [integerPayload] at h ⊢ <;> omega

/-- Explicit tree encoding of an integer: one sign bit and the binary natural
payload supplied by `DataEncode ℕ`. -/
instance integerDataEncode : DataEncode ℤ where
  encode z := DataEncode.encode (integerPayload z)
  h_inj := DataEncode.h_inj.comp integerPayload_injective

/-- A rational is represented by its canonical reduced numerator and positive
denominator.  These are fields of Lean's `Rat`, rather than an arbitrary
fraction representing the same number. -/
def rationalPayload (q : ℚ) : ℤ × ℕ := (q.num, q.den)

theorem rationalPayload_injective : Function.Injective rationalPayload := by
  intro p q h
  exact Rat.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

instance rationalDataEncode : DataEncode ℚ where
  encode q := DataEncode.encode (rationalPayload q)
  h_inj := DataEncode.h_inj.comp rationalPayload_injective

/-- Row-major list representation of a fixed-size matrix. -/
def rationalMatrixRows {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) : List (List ℚ) :=
  List.ofFn fun i ↦ List.ofFn fun j ↦ A i j

theorem rationalMatrixRows_injective {n : ℕ} :
    Function.Injective (@rationalMatrixRows n) := by
  intro A B hrows
  change List.ofFn (fun i ↦ List.ofFn (A i)) =
    List.ofFn (fun i ↦ List.ofFn (B i)) at hrows
  have houter := List.ofFn_injective hrows
  ext i j
  have hinner := congrFun houter i
  exact congrFun (List.ofFn_injective hinner) j

/-- Dimension followed by exactly `n` rows of exactly `n` rational entries. -/
def rationalMatrixInputPayload : RationalMatrixInput → ℕ × List (List ℚ)
  | ⟨n, A⟩ => (n, rationalMatrixRows A)

theorem rationalMatrixInputPayload_injective :
    Function.Injective rationalMatrixInputPayload := by
  intro x y h
  obtain ⟨n, A⟩ := x
  obtain ⟨m, B⟩ := y
  have hnm : n = m := congrArg Prod.fst h
  subst m
  have hrows : rationalMatrixRows A = rationalMatrixRows B :=
    congrArg Prod.snd h
  have hAB : A = B := rationalMatrixRows_injective hrows
  subst B
  rfl

instance rationalMatrixInputDataEncode : DataEncode RationalMatrixInput where
  encode x := DataEncode.encode (rationalMatrixInputPayload x)
  h_inj := DataEncode.h_inj.comp rationalMatrixInputPayload_injective

/-- An explicit injective binary code.  We retain injectivity in the structure
so no later complexity statement can silently identify distinct typed inputs. -/
structure OrdinaryBinaryEncoding (α : Type*) where
  /-- The finite binary word representing a value; injectivity is required by the encoding
  structure. -/
  encode : α → List Bool
  injective : Function.Injective encode

/-- The least-significant-bit-first binary expansion is injective, including
the convention `Nat.bits 0 = []`. -/
theorem natBits_injective : Function.Injective Nat.bits := by
  intro a b h
  have hrec : ∀ n : ℕ,
      n.bits.foldr (fun bit acc => Nat.bit bit acc) 0 = n := by
    intro n
    induction n using Nat.binaryRec' with
    | zero => simp
    | bit bit n hn ih =>
        rw [Nat.bits_append_bit n bit hn]
        simp [ih]
  have := congrArg (List.foldr (fun bit acc => Nat.bit bit acc) 0) h
  simpa [hrec] using this

/-- Canonical signed binary code.  `false` denotes `Int.ofNat`; `true`
denotes `Int.negSucc`.  The payload is an ordinary binary natural. -/
def integerBinaryCode (z : ℤ) : List Bool :=
  Int.casesOn z (fun n ↦ false :: n.bits) (fun n ↦ true :: n.bits)

@[simp] theorem integerBinaryRec_ofNat (n : ℕ) :
    Int.rec (fun k ↦ false :: k.bits) (fun k ↦ true :: k.bits)
      (Int.ofNat n) = false :: n.bits := by
  rfl

@[simp] theorem integerBinaryRec_natCast (n : ℕ) :
    Int.rec (fun k ↦ false :: k.bits) (fun k ↦ true :: k.bits) (n : ℤ) =
      false :: n.bits := by
  rfl

@[simp] theorem integerBinaryRec_negSucc (n : ℕ) :
    Int.rec (fun k ↦ false :: k.bits) (fun k ↦ true :: k.bits)
      (Int.negSucc n) = true :: n.bits := by
  rfl

@[simp] theorem integerBinaryRec_zero :
    Int.rec (fun n ↦ false :: n.bits) (fun n ↦ true :: n.bits) (0 : ℤ) =
      [false] := by
  rfl

@[simp] theorem integerBinaryRec_one :
    Int.rec (fun n ↦ false :: n.bits) (fun n ↦ true :: n.bits) (1 : ℤ) =
      [false, true] := by
  rfl

@[simp] theorem integerBinaryCode_ofNat (n : ℕ) :
    integerBinaryCode (Int.ofNat n) = false :: n.bits := by
  rfl

@[simp] theorem integerBinaryCode_negSucc (n : ℕ) :
    integerBinaryCode (Int.negSucc n) = true :: n.bits := by
  rfl

theorem integerBinaryCode_injective : Function.Injective integerBinaryCode := by
  intro a b h
  cases a with
  | ofNat a =>
      cases b with
      | ofNat b =>
          simp only [integerBinaryCode, List.cons.injEq, true_and] at h
          exact congrArg Int.ofNat (natBits_injective h)
      | negSucc b =>
          simp [integerBinaryCode] at h
  | negSucc a =>
      cases b with
      | ofNat b =>
          simp [integerBinaryCode] at h
      | negSucc b =>
          simp only [integerBinaryCode, List.cons.injEq, true_and] at h
          exact congrArg Int.negSucc (natBits_injective h)

/-- A natural-number code for integers.  Even naturals encode nonnegative
integers, while odd naturals encode `Int.negSucc`. -/
def integerNatCode (z : ℤ) : ℕ :=
  Int.casesOn z (fun n ↦ 2 * n) (fun n ↦ 2 * n + 1)

@[simp] theorem integerNatRec_ofNat (n : ℕ) :
    Int.rec (fun k ↦ 2 * k) (fun k ↦ 2 * k + 1) (Int.ofNat n) =
      2 * n := by
  rfl

@[simp] theorem integerNatRec_natCast (n : ℕ) :
    Int.rec (fun k ↦ 2 * k) (fun k ↦ 2 * k + 1) (n : ℤ) = 2 * n := by
  rfl

@[simp] theorem integerNatRec_negSucc (n : ℕ) :
    Int.rec (fun k ↦ 2 * k) (fun k ↦ 2 * k + 1) (Int.negSucc n) =
      2 * n + 1 := by
  rfl

@[simp] theorem integerNatRec_zero :
    Int.rec (fun n ↦ 2 * n) (fun n ↦ 2 * n + 1) (0 : ℤ) = 0 := by
  rfl

@[simp] theorem integerNatCode_ofNat (n : ℕ) :
    integerNatCode (Int.ofNat n) = 2 * n := by
  rfl

@[simp] theorem integerNatCode_negSucc (n : ℕ) :
    integerNatCode (Int.negSucc n) = 2 * n + 1 := by
  rfl

theorem integerNatCode_injective : Function.Injective integerNatCode := by
  intro a b h
  cases a with
  | ofNat a =>
      cases b with
      | ofNat b =>
          simp only [integerNatCode] at h
          exact congrArg Int.ofNat (by omega)
      | negSucc b =>
          have hparity := congrArg (fun n : ℕ => n % 2) h
          simp [integerNatCode] at hparity
  | negSucc a =>
      cases b with
      | ofNat b =>
          have hparity := congrArg (fun n : ℕ => n % 2) h
          simp [integerNatCode] at hparity
      | negSucc b =>
          simp only [integerNatCode] at h
          exact congrArg Int.negSucc (by omega)

/-- A matrix entry is stored as a self-delimiting pair, so a machine can
extract its numerator and denominator without first implementing arithmetic
unpairing. -/
def rationalEntryBinaryCode (q : ℚ) : List Bool :=
  pair (integerBinaryCode q.num) q.den.bits

theorem rationalEntryBinaryCode_injective :
    Function.Injective rationalEntryBinaryCode := by
  intro p q h
  obtain ⟨hnum, hden⟩ := pair_inj h
  exact Rat.ext (integerBinaryCode_injective hnum) (natBits_injective hden)

/-- A rational output is represented by one natural number: Szudzik's
pairing of the canonical integer code of its numerator and its positive
denominator. -/
def rationalNatCode (q : ℚ) : ℕ :=
  Nat.pair (integerNatCode q.num) q.den

theorem rationalNatCode_injective : Function.Injective rationalNatCode := by
  intro p q h
  have hpayload :
      integerNatCode p.num = integerNatCode q.num ∧ p.den = q.den :=
    Nat.pair_eq_pair.mp h
  exact Rat.ext (integerNatCode_injective hpayload.1) hpayload.2

/-- Canonical rational output code.  Using the ordinary binary expansion of
one natural makes every output bit accessible to the verified RAM decision
simulator. -/
def rationalBinaryCode (q : ℚ) : List Bool :=
  (rationalNatCode q).bits

theorem rationalBinaryCode_injective : Function.Injective rationalBinaryCode := by
  exact natBits_injective.comp rationalNatCode_injective

/-- Right-nested self-delimiting encoding of a finite list.  The empty list
is empty, while a nonempty list starts with the nonempty `pair` code. -/
def binaryListCode {α : Type*} (encode : α → List Bool) :
    List α → List Bool
  | [] => []
  | x :: xs => pair (encode x) (binaryListCode encode xs)

theorem binaryListCode_injective {α : Type*} {encode : α → List Bool}
    (hencode : Function.Injective encode) :
    Function.Injective (binaryListCode encode) := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hlen := congrArg List.length h
          simp [binaryListCode] at hlen
          omega
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil =>
          have hlen := congrArg List.length h
          simp [binaryListCode] at hlen
      | cons y ys =>
          simp only [binaryListCode] at h
          obtain ⟨hxy, hxsys⟩ := pair_inj h
          exact congrArg₂ List.cons (hencode hxy) (ih hxsys)

/-- Machine-facing matrix code: binary dimension followed by the right-nested
row list, whose rows and rational entries use the same canonical pairing
scheme. -/
def rationalMatrixBinaryCode (x : RationalMatrixInput) : List Bool :=
  pair x.1.bits
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      (rationalMatrixRows x.2))

theorem rationalMatrixBinaryCode_injective :
    Function.Injective rationalMatrixBinaryCode := by
  intro x y h
  obtain ⟨n, A⟩ := x
  obtain ⟨m, B⟩ := y
  simp only [rationalMatrixBinaryCode] at h
  obtain ⟨hnm, hrows⟩ := pair_inj h
  have hnm' : n = m := natBits_injective hnm
  subst m
  have hrowCode :
      Function.Injective (binaryListCode rationalEntryBinaryCode) :=
    binaryListCode_injective rationalEntryBinaryCode_injective
  have hrows' : rationalMatrixRows A = rationalMatrixRows B :=
    binaryListCode_injective hrowCode hrows
  have hAB : A = B := rationalMatrixRows_injective hrows'
  subst B
  rfl

/-- Canonical machine-facing binary encoding of one rational. -/
def rationalBinaryEncoding : OrdinaryBinaryEncoding ℚ where
  encode := rationalBinaryCode
  injective := rationalBinaryCode_injective

/-- Canonical machine-facing binary encoding of the dimension and row-major
matrix entries. -/
def rationalMatrixBinaryEncoding : OrdinaryBinaryEncoding RationalMatrixInput where
  encode := rationalMatrixBinaryCode
  injective := rationalMatrixBinaryCode_injective

/-- Length of the canonical parenthesized binary encoding of typed data. -/
def encodedBitLength (α : Type) [DataEncode α] (x : α) : ℕ :=
  (DataEncode.bitstringEncode x).length

theorem encodedBitLength_eq_dataSize
    {α : Type} [DataEncode α] (x : α) :
    encodedBitLength α x = (DataEncode.encode x).size := by
  simp [encodedBitLength, DataEncode.bitstringEncode_def]

/-- The canonical natural encoding contains, in particular, every bit of the
ordinary binary expansion. -/
theorem nat_size_le_encodedBitLength (n : ℕ) :
    n.size ≤ encodedBitLength ℕ n := by
  rw [encodedBitLength_eq_dataSize]
  change n.size ≤ (Data.l (n.bits.map fun b ↦ DataEncode.encode b)).size
  rw [← Nat.size_eq_bits_len]
  induction n.bits with
  | nil => simp
  | cons b bs ih =>
      cases b <;> simp [DataEncode.encode, Data.size] at ih ⊢ <;> omega

theorem nat_log_two_lt_encodedBitLength {n : ℕ} (hn : n ≠ 0) :
    Nat.log 2 n < encodedBitLength ℕ n := by
  exact (Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn)).trans_le
    (nat_size_le_encodedBitLength n)

@[simp] theorem integerPayload_snd (z : ℤ) :
    (integerPayload z).2 = z.natAbs := by
  cases z <;> simp [integerPayload]

theorem natAbs_encodedBitLength_lt_integer (z : ℤ) :
    encodedBitLength ℕ z.natAbs < encodedBitLength ℤ z := by
  rw [encodedBitLength_eq_dataSize, encodedBitLength_eq_dataSize]
  change (DataEncode.encode z.natAbs).size <
    (DataEncode.encode (integerPayload z)).size
  rw [DataEncode_pair]
  exact Data.size_lt_of_mem (by simp)

theorem denominator_encodedBitLength_lt_rational (q : ℚ) :
    encodedBitLength ℕ q.den < encodedBitLength ℚ q := by
  rw [encodedBitLength_eq_dataSize, encodedBitLength_eq_dataSize]
  change (DataEncode.encode q.den).size <
    (DataEncode.encode (rationalPayload q)).size
  rw [DataEncode_pair]
  exact Data.size_lt_of_mem (by simp [rationalPayload])

theorem numerator_encodedBitLength_lt_rational (q : ℚ) :
    encodedBitLength ℤ q.num < encodedBitLength ℚ q := by
  rw [encodedBitLength_eq_dataSize, encodedBitLength_eq_dataSize]
  change (DataEncode.encode q.num).size <
    (DataEncode.encode (rationalPayload q)).size
  rw [DataEncode_pair]
  exact Data.size_lt_of_mem (by simp [rationalPayload])

theorem numerator_natAbs_log_lt_rationalBitLength (q : ℚ)
    (hnum : q.num.natAbs ≠ 0) :
    Nat.log 2 q.num.natAbs < encodedBitLength ℚ q := by
  exact (nat_log_two_lt_encodedBitLength hnum).trans
    ((natAbs_encodedBitLength_lt_integer q.num).trans
      (numerator_encodedBitLength_lt_rational q))

theorem denominator_log_lt_rationalBitLength (q : ℚ) :
    Nat.log 2 q.den < encodedBitLength ℚ q := by
  exact (nat_log_two_lt_encodedBitLength q.den_nz).trans
    (denominator_encodedBitLength_lt_rational q)

/-- A positive rational is bounded below by a dyadic whose exponent is its
ordinary encoded length.  This is the elementary bridge from binary input
size to the lower-entry parameter used by the numerical optimizer. -/
theorem dyadic_encodedBitLength_lt_positive_rational
    {q : ℚ} (hq : 0 < q) :
    (1 / 2 : ℚ) ^ encodedBitLength ℚ q < q := by
  let L := encodedBitLength ℚ q
  have hdenlog : Nat.log 2 q.den < L := denominator_log_lt_rationalBitLength q
  have hdenpow : q.den < 2 ^ L := Nat.lt_pow_of_log_lt (by norm_num) hdenlog
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  have hnum0 : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hnum.ne'
  have hnum1 : 1 ≤ q.num.natAbs := Nat.one_le_iff_ne_zero.mpr hnum0
  have hnumabs : (q.num.natAbs : ℤ) = q.num :=
    Int.natAbs_of_nonneg hnum.le
  have hqrep : q = (q.num.natAbs : ℚ) / (q.den : ℚ) := by
    calc
      q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
      _ = (q.num.natAbs : ℚ) / (q.den : ℚ) := by
        congr 1
        change (q.num : ℚ) = ((q.num.natAbs : ℤ) : ℚ)
        rw [hnumabs]
  have hdenpowQ : (q.den : ℚ) < (2 : ℚ) ^ L := by exact_mod_cast hdenpow
  have hrecip : 1 / (2 : ℚ) ^ L < 1 / (q.den : ℚ) := by
    exact one_div_lt_one_div_of_lt (by positivity) hdenpowQ
  calc
    (1 / 2 : ℚ) ^ L = 1 / (2 : ℚ) ^ L := by
      simp only [one_div, inv_pow]
    _ < 1 / (q.den : ℚ) := hrecip
    _ ≤ (q.num.natAbs : ℚ) / (q.den : ℚ) := by
      have hnum1Q : (1 : ℚ) ≤ (q.num.natAbs : ℚ) := by
        exact_mod_cast hnum1
      exact div_le_div_of_nonneg_right hnum1Q
        (by positivity : (0 : ℚ) ≤ (q.den : ℚ))
    _ = q := hqrep.symm

/-- The same canonical binary length also gives a coarse dyadic upper bound
on every positive rational. -/
theorem positive_rational_lt_two_pow_encodedBitLength
    {q : ℚ} (hq : 0 < q) :
    q < (2 : ℚ) ^ encodedBitLength ℚ q := by
  let L := encodedBitLength ℚ q
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  have hnum0 : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hnum.ne'
  have hnumlog : Nat.log 2 q.num.natAbs < L :=
    numerator_natAbs_log_lt_rationalBitLength q hnum0
  have hnumpow : q.num.natAbs < 2 ^ L :=
    Nat.lt_pow_of_log_lt (by norm_num) hnumlog
  have hnumabs : (q.num.natAbs : ℤ) = q.num :=
    Int.natAbs_of_nonneg hnum.le
  have hqrep : q = (q.num.natAbs : ℚ) / (q.den : ℚ) := by
    calc
      q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
      _ = (q.num.natAbs : ℚ) / (q.den : ℚ) := by
        congr 1
        change (q.num : ℚ) = ((q.num.natAbs : ℤ) : ℚ)
        rw [hnumabs]
  have hdenNat : 1 ≤ q.den := Nat.one_le_iff_ne_zero.mpr q.den_nz
  have hden : (1 : ℚ) ≤ q.den := by exact_mod_cast hdenNat
  have hquot : (q.num.natAbs : ℚ) / (q.den : ℚ) ≤
      (q.num.natAbs : ℚ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℚ) < q.den)]
    have hnumQ : (0 : ℚ) ≤ q.num.natAbs := by positivity
    nlinarith
  calc
    q = (q.num.natAbs : ℚ) / (q.den : ℚ) := hqrep
    _ ≤ (q.num.natAbs : ℚ) := hquot
    _ < (2 : ℚ) ^ encodedBitLength ℚ q := by
      simpa only [L] using (show (q.num.natAbs : ℚ) < (2 : ℚ) ^ L by
        exact_mod_cast hnumpow)

/-- A deliberately simple common bit bound for all entries of a fixed-size
rational matrix.  The sum, rather than a maximum, keeps the definition
primitive and gives an immediate polynomial bound. -/
def rationalMatrixEntryBitBound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  1 + ∑ i, ∑ j, encodedBitLength ℚ (A i j)

theorem entry_encodedBitLength_lt_matrixBound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    encodedBitLength ℚ (A i j) < rationalMatrixEntryBitBound A := by
  have hrow : encodedBitLength ℚ (A i j) ≤
      ∑ k, encodedBitLength ℚ (A i k) :=
    Finset.single_le_sum
      (f := fun k ↦ encodedBitLength ℚ (A i k))
      (fun k _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  have hmatrix : (∑ k, encodedBitLength ℚ (A i k)) ≤
      ∑ l, ∑ k, encodedBitLength ℚ (A l k) :=
    Finset.single_le_sum
      (f := fun l ↦ ∑ k, encodedBitLength ℚ (A l k))
      (fun l _ ↦ Finset.sum_nonneg fun k _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)
  simp only [rationalMatrixEntryBitBound]
  omega

/-- Every positive entry is bounded below by the same dyadic determined by
the matrix encoding. -/
theorem matrix_dyadic_bitBound_lt_entry {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℚ} (hA : ∀ i j, 0 < A i j)
    (i j : Fin n) :
    (1 / 2 : ℚ) ^ rationalMatrixEntryBitBound A < A i j := by
  have hlen := (entry_encodedBitLength_lt_matrixBound A i j).le
  have hpow : (1 / 2 : ℚ) ^ rationalMatrixEntryBitBound A ≤
      (1 / 2 : ℚ) ^ encodedBitLength ℚ (A i j) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hlen
  exact hpow.trans_lt (dyadic_encodedBitLength_lt_positive_rational (hA i j))

/-- Bundle a dimension-indexed rational-matrix algorithm into a single typed
function. -/
def bundledAlgorithm
    (alg : ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ)
    (x : RationalMatrixInput) : ℚ :=
  alg x.1 x.2

/-- A total string function realizes a typed matrix algorithm when it produces
the canonical rational encoding on every canonically encoded matrix input.
Its behavior on malformed strings is deliberately unrestricted. -/
def StringRealizes
    (F : List Bool → List Bool)
    (alg : ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ) : Prop :=
  ∀ x : RationalMatrixInput,
    F (rationalMatrixBinaryCode x) =
      rationalBinaryCode (bundledAlgorithm alg x)

/-- The concrete polynomial-time assertion used in Theorem 1.  `FP` is
Complexitylib's deterministic multitape-Turing-machine class with a polynomial
step bound. -/
def RunsInPolynomialTime
    (alg : ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ) : Prop :=
  ∃ F : List Bool → List Bool, F ∈ Complexity.FP ∧ StringRealizes F alg

end BeyondBethe
