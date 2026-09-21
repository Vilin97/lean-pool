/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.BlockCycle

/-!
# The block trace factorization

The trace of a block permutation against the block-diagonal power
factors into cycle traces of the block endomorphism — the engine
of the Frobenius identity at every ambient arity.

The `S_k`-level cycle normal form transports through the
block-permutation homomorphism for free; the tensor-splitting
slices carry `finCongr` casts because `n·(a+b) = n·a + n·b` is
propositional, managed by the arity-cast transport `endCast`.
-/

namespace RS

open CategoryTheory

variable {R : ℕ} (f : EdgeRankParameter R)

/-! ### Trace cyclicity -/

/-- The skein trace is cyclic. -/
private theorem skeinTrace_mul_comm' (n : ℕ)
    (u v : skeinEnd f n) :
    skeinTrace f n (u * v) = skeinTrace f n (v * u) :=
  HomSpace.traceMap_comp_comm f v u

/-- The skein trace is conjugation invariant. -/
private theorem skeinTrace_conj' (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (x : skeinEnd f n) :
    skeinTrace f n
      (permClass f n σ * x * permClass f n σ⁻¹) =
    skeinTrace f n x := by
  rw [skeinTrace_mul_comm', ← mul_assoc,
    show permClass f n σ⁻¹ * permClass f n σ =
      permClass f n (σ⁻¹ * σ) from
      (map_mul (permToEnd f n) σ⁻¹ σ).symm,
    inv_mul_cancel,
    show permClass f n (1 : Equiv.Perm (Fin n)) =
      (1 : skeinEnd f n) from map_one (permToEnd f n),
    one_mul]

/-! ### Arity-cast transport -/

/-- Transport of a strand endomorphism along an arity equality:
conjugation by the boundary cast. -/
noncomputable def endCast {a b : ℕ} (h : a = b)
    (x : skeinEnd f a) : skeinEnd f b :=
  h ▸ x

/-- Cast transport preserves the trace. -/
theorem skeinTrace_endCast {a b : ℕ} (h : a = b)
    (x : skeinEnd f a) :
    skeinTrace f b (endCast f h x) = skeinTrace f a x := by
  cases h
  rfl

/-- Cast transport is multiplicative. -/
theorem endCast_mul {a b : ℕ} (h : a = b)
    (x y : skeinEnd f a) :
    endCast f h (x * y) = endCast f h x * endCast f h y := by
  cases h
  rfl

/-! ### Block tensor calculus -/

/-- Arity cast interacts with `permClass`: transporting a permutation
class along an arity equality gives the permutation class of the
cast permutation. -/
private theorem endCast_permClass {a b : ℕ} (h : a = b)
    (σ : Equiv.Perm (Fin a)) :
    endCast f h (permClass f a σ) =
      permClass f b ((finCongr h).permCongr σ) := by
  subst h
  show permClass f a σ = permClass f a _
  congr 1

/-- `permClass_sumCongr` stated for `blockTensorEnd`. -/
private theorem permClass_blockTensorEnd (a b : ℕ)
    (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) :
    permClass f (a + b)
      (finSumFinEquiv.permCongr (Equiv.sumCongr σ τ)) =
      blockTensorEnd f (permClass f a σ) (permClass f b τ) :=
  permClass_sumCongr f a b σ τ

/-- Block-wise commutativity lifts through the block tensor. -/
private theorem blockTensorEnd_comm {a b : ℕ}
    (P G : skeinEnd f a) (Q H : skeinEnd f b)
    (hPG : P * G = G * P) (hQH : Q * H = H * Q) :
    blockTensorEnd f P Q * blockTensorEnd f G H =
      blockTensorEnd f G H * blockTensorEnd f P Q := by
  rw [blockTensorEnd_mul, hPG, hQH, ← blockTensorEnd_mul]

/-- `bundleMapClass` of a self-cast is the identity class. -/
private theorem bmc_finCongr_self {n : ℕ} (h : n = n) :
    bundleMapClass f (finCongr h) =
      HomSpace.ofFragment f.val (strandBundle n) := by
  rw [show finCongr h = _root_.Equiv.refl (Fin n) from
    _root_.Equiv.ext (fun x => Fin.ext rfl)]
  exact bundleMapClass_refl f n

/-- `bundleMapClass` of the symm of a self-cast is the identity. -/
private theorem bmc_finCongr_symm_self {n : ℕ} (h : n = n) :
    bundleMapClass f ((finCongr h).symm) =
      HomSpace.ofFragment f.val (strandBundle n) := by
  rw [show (finCongr h).symm = _root_.Equiv.refl (Fin n) from
    _root_.Equiv.ext (fun x => Fin.ext rfl)]
  exact bundleMapClass_refl f n

/-- `endCast` is conjugation by `bundleMapClass (finCongr h)`. -/
private theorem endCast_eq_conj {a b : ℕ} (h : a = b)
    (x : skeinEnd f a) :
    (h ▸ x : skeinEnd f b) =
    HomSpace.comp f b a b
      (bundleMapClass f ((finCongr h).symm))
      (HomSpace.comp f a a b
        (x : SkeinObj.mk (f := f) a ⟶ SkeinObj.mk a)
        (bundleMapClass f (finCongr h))) := by
  cases h
  -- After cases h, b = a, need x = comp(bmc(.symm), comp(x, bmc(.)))
  -- Use ∀-quantified key to avoid type-mismatch at implicit transparency
  have key : ∀ (p : a = a),
      HomSpace.comp f a a a
        (bundleMapClass f ((finCongr p).symm))
        (HomSpace.comp f a a a
          (show HomSpace f.val (a + a) from x)
          (bundleMapClass f (finCongr p))) =
        (show HomSpace f.val (a + a) from x) := by
    intro p
    rw [bmc_finCongr_self f p, bmc_finCongr_symm_self f p,
      HomSpace.comp_id_right, HomSpace.comp_id_left]
  exact (key _).symm

/-- Pushing `endCast` through the left argument of `blockTensorEnd`. -/
private theorem endCast_blockTensorEnd_left {a a' b : ℕ} (h : a = a')
    (u : skeinEnd f a) (v : skeinEnd f b) :
    blockTensorEnd f (endCast f h u) v =
      endCast f (show a + b = a' + b by rw [h]) (blockTensorEnd f u v) := by
  cases h; rfl

/-- Composing two `endCast` transports. -/
private theorem endCast_trans {a b c : ℕ} (h₁ : a = b) (h₂ : b = c)
    (x : skeinEnd f a) :
    endCast f h₂ (endCast f h₁ x) = endCast f (h₁.trans h₂) x := by
  cases h₂; cases h₁; rfl

/-- An `endCast` along a self-equality is the identity. -/
private theorem endCast_rfl (x : skeinEnd f a) (h : a = a) :
    endCast f h x = x := by
  have : h = Eq.refl a := rfl
  subst this; rfl

/-- Tensor with the zero-arity identity is the identity. -/
private theorem blockTensorEnd_one_right (x : skeinEnd f a) :
    blockTensorEnd f x (1 : skeinEnd f 0) = x := by
  have h := rightUnitNat_class f (show HomSpace f.val (a + a) from x)
  have hcast : ∀ hp : a + 0 = a,
      bundleMapClass f (finCongr hp) =
        HomSpace.ofFragment f.val (strandBundle a) := by
    intro hp
    rw [show finCongr hp = _root_.Equiv.refl (Fin a) from
      _root_.Equiv.ext (fun x => Fin.ext rfl)]
    exact bundleMapClass_refl f a
  simp only [hcast] at h
  exact (HomSpace.comp_id_right f a a
      (blockTensorEnd f x (1 : skeinEnd f 0))).symm.trans
    (h.trans (HomSpace.comp_id_left f a a x))

-- Raised budget: associativity is stated up to an arity cast, so
-- the cast transport is unfolded on both sides.
/-- Tensor associativity for `blockTensorEnd`, up to `endCast`. -/
private theorem blockTensor_assoc {a b c : ℕ}
    (p₁ : skeinEnd f a) (p₂ : skeinEnd f b) (p₃ : skeinEnd f c) :
    endCast f (show (a + b) + c = a + (b + c) by omega)
        (blockTensorEnd f (blockTensorEnd f p₁ p₂) p₃) =
    blockTensorEnd f p₁ (blockTensorEnd f p₂ p₃) := by
  set h : (a + b) + c = a + (b + c) := by omega
  -- Rewrite endCast as conjugation by the associator
  show (h ▸ blockTensorEnd f (blockTensorEnd f p₁ p₂) p₃ :
      skeinEnd f (a + (b + c))) =
    blockTensorEnd f p₁ (blockTensorEnd f p₂ p₃)
  rw [endCast_eq_conj f h]
  -- Use associator naturality
  have hassoc := assocNat_class f
    (show HomSpace f.val (a + a) from p₁)
    (show HomSpace f.val (b + b) from p₂)
    (show HomSpace f.val (c + c) from p₃)
  -- Rewrite the inner composition using hassoc
  conv_lhs =>
    rw [show HomSpace.comp f ((a + b) + c) ((a + b) + c) (a + (b + c))
        (show HomSpace f.val (((a + b) + c) + ((a + b) + c)) from
          blockTensorEnd f (blockTensorEnd f p₁ p₂) p₃)
        (bundleMapClass f (finCongr h)) =
      HomSpace.comp f ((a + b) + c) (a + (b + c)) (a + (b + c))
        (bundleMapClass f (finCongr h))
        (show HomSpace f.val ((a + (b + c)) + (a + (b + c))) from
          blockTensorEnd f p₁ (blockTensorEnd f p₂ p₃)) from hassoc]
  -- Now: comp(α⁻¹, comp(α, RHS)) = RHS
  rw [← HomSpace.comp_assoc]
  -- comp(comp(α⁻¹, α), RHS) = RHS
  have hcancel : HomSpace.comp f (a + (b + c)) ((a + b) + c) (a + (b + c))
      (bundleMapClass f ((finCongr h).symm))
      (bundleMapClass f (finCongr h)) =
    HomSpace.ofFragment f.val (strandBundle (a + (b + c))) := by
    rw [bundleMapClass_comp,
      show (finCongr h).symm.trans (finCongr h) =
        _root_.Equiv.refl (Fin (a + (b + c))) from
        _root_.Equiv.ext (fun x => by simp [finCongr])]
    exact bundleMapClass_refl f _
  rw [hcancel, HomSpace.comp_id_left]

/-- `blockPow` splits as a tensor of two parts, modulo arity cast. -/
private theorem blockPow_split (n : ℕ) (g : skeinEnd f n) (a : ℕ) :
    ∀ b : ℕ,
    endCast f (Nat.mul_add n a b) (blockPow f n g (a + b)) =
      blockTensorEnd f (blockPow f n g a) (blockPow f n g b) := by
  intro b
  induction b with
  | zero =>
      show blockPow f n g a =
        blockTensorEnd f (blockPow f n g a) (1 : skeinEnd f (n * 0))
      exact (blockTensorEnd_one_right f (blockPow f n g a)).symm
  | succ k ih =>
      -- blockPow (a + (k+1)) = blockTensorEnd f (blockPow (a+k)) g
      show endCast f (Nat.mul_add n a (k + 1))
          (blockTensorEnd f (blockPow f n g (a + k)) g) =
        blockTensorEnd f (blockPow f n g a)
          (blockTensorEnd f (blockPow f n g k) g)
      -- Substitute blockPow (a+k) using IH
      have hih : blockPow f n g (a + k) =
          endCast f (Nat.mul_add n a k).symm
            (blockTensorEnd f (blockPow f n g a)
              (blockPow f n g k)) := by
        rw [← ih, endCast_trans, endCast_rfl]
      rw [hih, endCast_blockTensorEnd_left, endCast_trans]
      -- Now have: endCast f h ((blockPow a ⊗ blockPow k) ⊗ g)
      exact blockTensor_assoc f
        (blockPow f n g a) (blockPow f n g k) g

/-- `blockPerm n` distributes over `sumCongr`, modulo arity cast. -/
private theorem blockPerm_sumCongr (n : ℕ) {a b : ℕ}
    (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) :
    (finCongr (Nat.mul_add n a b)).permCongr
      (blockPerm n (finSumFinEquiv.permCongr (Equiv.sumCongr σ τ))) =
    finSumFinEquiv.permCongr
      (Equiv.sumCongr (blockPerm n σ) (blockPerm n τ)) := by
  by_cases hn : n = 0
  · -- ═══════ n = 0: THE INDEX TYPE IS EMPTY ═══════
    subst hn; ext ⟨v, hv⟩; simp at hv
  · -- ═══════ 0 < n ═══════
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    ext ⟨v, hv⟩
    -- Goal is a .val equality after ext
    -- Decompose v = n * q + r
    have hv' : v < n * (a + b) := by
      calc v < n * a + n * b := hv
        _ = n * (a + b) := (Nat.mul_add n a b).symm
    have hqab : v / n < a + b := Nat.div_lt_of_lt_mul hv'
    have hrn : v % n < n := Nat.mod_lt v hn'
    have hv_eq : v = n * (v / n) + v % n := (Nat.div_add_mod v n).symm
    -- Compute LHS via blockPerm_val
    set π := finSumFinEquiv.permCongr (Equiv.sumCongr σ τ) with hπ_def
    have hbp_lhs := blockPerm_val n π ⟨v / n, hqab⟩ ⟨v % n, hrn⟩
    -- LHS.val = n * (π ⟨v/n, _⟩).val + v%n
    have hLHS : ((finCongr (Nat.mul_add n a b)).permCongr
        (blockPerm n π) ⟨v, hv⟩).val =
        n * (π ⟨v / n, hqab⟩).val + v % n := by
      rw [Equiv.permCongr_apply]
      rw [show ((finCongr (Nat.mul_add n a b)).symm ⟨v, hv⟩ :
          Fin (n * (a + b))) =
        ⟨n * (v / n) + v % n, hv_eq ▸ hv'⟩ from Fin.ext hv_eq]
      rw [hbp_lhs]
      rfl
    -- Case split on v / n < a
    by_cases hqa : v / n < a
    · -- v is in the first a blocks
      have hvna : v < n * a := by
        have := (Nat.div_lt_iff_lt_mul hn').mp hqa -- v < a * n
        calc v < a * n := this
          _ = n * a := Nat.mul_comm a n
      -- Compute π(v/n) = σ(v/n)
      have hπq : (π ⟨v / n, hqab⟩).val = (σ ⟨v / n, hqa⟩).val := by
        rw [hπ_def]
        show (finSumFinEquiv (Equiv.sumCongr σ τ
          (finSumFinEquiv.symm ⟨v / n, hqab⟩))).val = _
        rw [show (⟨v / n, hqab⟩ : Fin (a + b)) =
          Fin.castAdd b ⟨v / n, hqa⟩ from Fin.ext rfl,
          finSumFinEquiv_symm_apply_castAdd]
        simp [Equiv.sumCongr_apply, finSumFinEquiv_apply_left,
          Fin.castAdd]
      -- Compute RHS: v < n*a, so in left summand
      have hRHS : (finSumFinEquiv.permCongr
          (Equiv.sumCongr (blockPerm n σ) (blockPerm n τ))
          ⟨v, hv⟩).val =
          n * (σ ⟨v / n, hqa⟩).val + v % n := by
        show (finSumFinEquiv (Equiv.sumCongr (blockPerm n σ)
          (blockPerm n τ) (finSumFinEquiv.symm ⟨v, hv⟩))).val = _
        rw [show (⟨v, hv⟩ : Fin (n * a + n * b)) =
          Fin.castAdd (n * b) ⟨v, hvna⟩ from Fin.ext rfl,
          finSumFinEquiv_symm_apply_castAdd]
        simp only [Equiv.sumCongr_apply]
        conv_lhs =>
          rw [show (⟨v, hvna⟩ : Fin (n * a)) =
            ⟨n * (v / n) + v % n, hv_eq ▸ hvna⟩ from Fin.ext hv_eq]
        exact congrArg Fin.val
          (blockPerm_val n σ ⟨v / n, hqa⟩ ⟨v % n, hrn⟩)
      rw [hLHS, hπq, hRHS]
    · -- v is in the last b blocks (v / n ≥ a)
      have hqa' : a ≤ v / n := Nat.le_of_not_lt hqa
      have hvna : n * a ≤ v := by
        calc n * a
          _ = a * n := Nat.mul_comm n a
          _ ≤ (v / n) * n := Nat.mul_le_mul_right n hqa'
          _ ≤ v := Nat.div_mul_le_self v n
      have hqb : v / n - a < b := by omega
      -- Compute π(v/n) = a + τ(v/n - a)
      have hπq : (π ⟨v / n, hqab⟩).val =
          a + (τ ⟨v / n - a, hqb⟩).val := by
        rw [hπ_def]
        show (finSumFinEquiv (Equiv.sumCongr σ τ
          (finSumFinEquiv.symm ⟨v / n, hqab⟩))).val = _
        rw [show (⟨v / n, hqab⟩ : Fin (a + b)) =
          Fin.natAdd a ⟨v / n - a, hqb⟩ from
            Fin.ext (show v / n = a + (v / n - a) by omega),
          finSumFinEquiv_symm_apply_natAdd]
        simp [Equiv.sumCongr_apply, finSumFinEquiv_apply_right,
          Fin.natAdd]
      -- Shift arithmetic
      have h_nsub : n * (v / n - a) + n * a = n * (v / n) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hqa']
      have h_shift : v - n * a = n * (v / n - a) + v % n := by
        have := (Nat.div_add_mod v n).symm; omega
      have hshift_div : (v - n * a) / n = v / n - a := by
        rw [h_shift, Nat.mul_add_div hn', Nat.div_eq_of_lt hrn]
        omega
      have hshift_mod : (v - n * a) % n = v % n := by
        rw [h_shift, Nat.mul_add_mod, Nat.mod_eq_of_lt hrn]
      -- Pre-compute blockPerm on the shifted element
      have hbp_shifted : (blockPerm n τ
          ⟨v - n * a, by omega⟩).val =
          n * (τ ⟨v / n - a, hqb⟩).val + v % n := by
        have hbound' : n * (v / n - a) + v % n < n * b := by
          rw [show n * (v / n - a) + v % n = v - n * a from
            h_shift.symm]; omega
        conv_lhs =>
          rw [show (⟨v - n * a, (by omega : v - n * a < n * b)⟩ :
              Fin (n * b)) =
            ⟨n * (v / n - a) + v % n, hbound'⟩ from
              Fin.ext h_shift]
        exact congrArg Fin.val
          (blockPerm_val n τ ⟨v / n - a, hqb⟩ ⟨v % n, hrn⟩)
      -- Compute RHS
      have hRHS : (finSumFinEquiv.permCongr
          (Equiv.sumCongr (blockPerm n σ) (blockPerm n τ))
          ⟨v, hv⟩).val =
          n * a + (n * (τ ⟨v / n - a, hqb⟩).val + v % n) := by
        show (finSumFinEquiv (Equiv.sumCongr (blockPerm n σ)
          (blockPerm n τ) (finSumFinEquiv.symm ⟨v, hv⟩))).val = _
        rw [show (⟨v, hv⟩ : Fin (n * a + n * b)) =
          Fin.natAdd (n * a) ⟨v - n * a, by omega⟩ from
            Fin.ext (Nat.add_sub_cancel' hvna).symm,
          finSumFinEquiv_symm_apply_natAdd]
        simp only [Equiv.sumCongr_apply, Sum.map_inr,
          finSumFinEquiv_apply_right, Fin.natAdd, Fin.val_mk]
        congr 1
      rw [hLHS, hπq, hRHS]; ring

/-! ### Braiding commutativity at block arities -/

-- Raised budget: the commutation is checked at the HomSpace level,
-- where the tensor and the bundle map both expand.
/-- The braiding `β_{n,n}` commutes with `g ⊗ g` at the HomSpace
level. -/
private theorem braiding_comm_block (n : ℕ)
    (g' : HomSpace f.val (n + n)) :
    HomSpace.comp f (n + n) (n + n) (n + n)
      (HomSpace.tensor f n n n n g' g')
      (bundleMapClass f (transposeEquiv n n)) =
    HomSpace.comp f (n + n) (n + n) (n + n)
      (bundleMapClass f (transposeEquiv n n))
      (HomSpace.tensor f n n n n g' g') := by
  have h1 : HomSpace.tensor f n n n n g' g' =
      HomSpace.comp f (n + n) (n + n) (n + n)
        (HomSpace.tensor f n n n n g'
          (HomSpace.ofFragment f.val (strandBundle n)))
        (HomSpace.tensor f n n n n
          (HomSpace.ofFragment f.val (strandBundle n)) g') := by
    have := HomSpace.tensor_comp f g'
      (HomSpace.ofFragment f.val (strandBundle n))
      (HomSpace.ofFragment f.val (strandBundle n)) g'
    rw [HomSpace.comp_id_right, HomSpace.comp_id_left] at this
    exact this
  have h2 : HomSpace.tensor f n n n n g' g' =
      HomSpace.comp f (n + n) (n + n) (n + n)
        (HomSpace.tensor f n n n n
          (HomSpace.ofFragment f.val (strandBundle n)) g')
        (HomSpace.tensor f n n n n g'
          (HomSpace.ofFragment f.val (strandBundle n))) := by
    have := HomSpace.tensor_comp f
      (HomSpace.ofFragment f.val (strandBundle n)) g' g'
      (HomSpace.ofFragment f.val (strandBundle n))
    rw [HomSpace.comp_id_left, HomSpace.comp_id_right] at this
    exact this
  conv_lhs => rw [h1]
  rw [HomSpace.comp_assoc f (n + n) (n + n) (n + n) (n + n)]
  rw [braidNatRight_class f n g']
  rw [← HomSpace.comp_assoc f (n + n) (n + n) (n + n) (n + n)]
  rw [braidNatLeft_class f n g']
  rw [HomSpace.comp_assoc f (n + n) (n + n) (n + n) (n + n)]
  rw [← h2]

/-- The braiding at block arities commutes with `g ⊗ g` at the
End level. -/
private theorem blockSwap01_comm (n : ℕ) (g : skeinEnd f n) :
    permClass f (n + n) (transposeEquiv n n) *
      blockTensorEnd f g g =
    blockTensorEnd f g g *
      permClass f (n + n) (transposeEquiv n n) := by
  show HomSpace.comp f (n + n) (n + n) (n + n)
      (show HomSpace f.val _ from blockTensorEnd f g g)
      (show HomSpace f.val _ from
        permClass f (n + n) (transposeEquiv n n)) =
    HomSpace.comp f (n + n) (n + n) (n + n)
      (show HomSpace f.val _ from
        permClass f (n + n) (transposeEquiv n n))
      (show HomSpace f.val _ from blockTensorEnd f g g)
  rw [permClass_eq_bundleMapClass]
  exact braiding_comm_block f n (show HomSpace f.val (n + n) from g)

/-! ### Swap commutativity at block level -/

/-- A swap fixing the last element decomposes as a tensor with
    identity on the last position. -/
private theorem swap_internal_block' {m : ℕ}
    (i : ℕ) (hi : i + 2 ≤ m) :
    Equiv.swap (⟨i, by omega⟩ : Fin (m + 1))
      (⟨i + 1, by omega⟩ : Fin (m + 1)) =
    finSumFinEquiv.permCongr (Equiv.sumCongr
      (Equiv.swap (⟨i, by omega⟩ : Fin m) ⟨i + 1, by omega⟩)
      (1 : Equiv.Perm (Fin 1))) := by
  ext ⟨z, hz⟩
  simp only [Equiv.permCongr_apply]
  by_cases hz1 : z < m
  · have hsym : finSumFinEquiv.symm ⟨z, hz⟩ =
        Sum.inl ⟨z, hz1⟩ :=
      finSumFinEquiv_symm_apply_castAdd ⟨z, hz1⟩
    rw [hsym]
    simp only [Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.swap_apply_def]
    split_ifs <;>
      simp_all [finSumFinEquiv_apply_left, Fin.ext_iff]
  · have hzm : z = m := by omega
    have hsym : finSumFinEquiv.symm ⟨z, hz⟩ =
        Sum.inr (⟨0, by omega⟩ : Fin 1) := by
      have : (⟨z, hz⟩ : Fin (m + 1)) =
          Fin.natAdd m ⟨0, by omega⟩ :=
        Fin.ext (by simp [Fin.natAdd]; omega)
      rw [this, finSumFinEquiv_symm_apply_natAdd]
    rw [hsym]
    simp only [Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.Perm.one_apply, Equiv.swap_apply_def]
    split_ifs <;>
      simp_all [finSumFinEquiv_apply_right, Fin.ext_iff,
        Fin.natAdd] <;>
      omega

/-- A swap of the last two elements decomposes as identity tensor
    swap on the last two positions. -/
private theorem swap_last_block' (m' : ℕ) :
    Equiv.swap (⟨m', by omega⟩ : Fin (m' + 2))
      (⟨m' + 1, by omega⟩ : Fin (m' + 2)) =
    finSumFinEquiv.permCongr (Equiv.sumCongr
      (1 : Equiv.Perm (Fin m'))
      (Equiv.swap (0 : Fin 2) (1 : Fin 2))) := by
  ext ⟨z, hz⟩
  simp only [Equiv.permCongr_apply]
  by_cases hz1 : z < m'
  · have hsym : finSumFinEquiv.symm ⟨z, hz⟩ =
        Sum.inl ⟨z, hz1⟩ :=
      finSumFinEquiv_symm_apply_castAdd ⟨z, hz1⟩
    rw [hsym]
    simp only [Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.Perm.one_apply, Equiv.swap_apply_def]
    split_ifs <;>
      simp_all [finSumFinEquiv_apply_left, Fin.ext_iff] <;>
      omega
  · have hz2 : z - m' < 2 := by omega
    have hsym : finSumFinEquiv.symm ⟨z, hz⟩ =
        Sum.inr ⟨z - m', hz2⟩ := by
      have : (⟨z, hz⟩ : Fin (m' + 2)) =
          Fin.natAdd m' ⟨z - m', hz2⟩ :=
        Fin.ext (by simp [Fin.natAdd]; omega)
      rw [this, finSumFinEquiv_symm_apply_natAdd]
    rw [hsym]
    simp only [Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.swap_apply_def]
    split_ifs <;>
      simp_all [finSumFinEquiv_apply_right, Fin.ext_iff,
        Fin.natAdd] <;>
      omega

/-- `blockPerm n (swap 0 1)`, cast from arity `n * 2` to
    `n * 1 + n * 1`, equals the transpose equivalence. -/
private theorem blockPerm_swap01_eq_transposeEquiv (n : ℕ) :
    (finCongr (Nat.mul_add n 1 1)).permCongr
      (blockPerm n (Equiv.swap (0 : Fin 2) 1)) =
    transposeEquiv (n * 1) (n * 1) := by
  by_cases hn : n = 0
  · subst hn; ext ⟨v, hv⟩; simp at hv
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    ext ⟨v, hv⟩ : 1
    simp only [Equiv.permCongr_apply]
    apply Fin.ext
    -- finCongr doesn't change .val, so reduce to blockPerm
    have hv2 : v < n * 2 := by omega
    show (blockPerm n (Equiv.swap (0 : Fin 2) 1)
        ⟨v, hv2⟩).val =
      (transposeEquiv (n * 1) (n * 1) ⟨v, hv⟩).val
    by_cases hvn : v < n
    · -- Block 0 → block 1
      have hlhs : (blockPerm n (Equiv.swap (0 : Fin 2) 1)
            ⟨v, hv2⟩).val = n + v := by
        have h0 : (⟨v, hv2⟩ : Fin (n * 2)) =
            ⟨n * 0 + v, by omega⟩ :=
          Fin.ext (by simp only []; omega)
        rw [h0]
        have h1 := congrArg Fin.val (blockPerm_val n
            (Equiv.swap (0 : Fin 2) 1)
            ⟨0, by omega⟩ ⟨v, hvn⟩)
        simp only [] at h1
        rw [h1]
        simp []
      rw [hlhs, transposeEquiv_low (n * 1) (n * 1) v
        (by omega) hv (by omega)]
      simp only []; omega
    · -- Block 1 → block 0
      push Not at hvn
      have hlhs : (blockPerm n (Equiv.swap (0 : Fin 2) 1)
            ⟨v, hv2⟩).val = v - n := by
        have h0 : (⟨v, hv2⟩ : Fin (n * 2)) =
            ⟨n * 1 + (v - n), by omega⟩ :=
          Fin.ext (by simp only []; omega)
        rw [h0]
        have h1 := congrArg Fin.val (blockPerm_val n
            (Equiv.swap (0 : Fin 2) 1)
            ⟨1, by omega⟩ ⟨v - n, by omega⟩)
        simp only [] at h1
        rw [h1]
        simp []
      have hrhs_eq : (⟨v, hv⟩ : Fin (n * 1 + n * 1)) =
          ⟨n * 1 + (v - n * 1), by omega⟩ :=
        Fin.ext (by simp only []; omega)
      rw [hlhs, hrhs_eq, transposeEquiv_high (n * 1) (n * 1)
        (v - n * 1) (by omega) (by omega) (by omega)]
      simp only []; omega

/-- The block swap `blockPerm n (swap 0 1)` commutes with
    `blockPow 2`, proved by casting to arity `n * 1 + n * 1`
    and applying `blockSwap01_comm`. -/
private theorem swap01_comm_blockPow2 (g : skeinEnd f n) :
    permClass f (n * 2)
        (blockPerm n (Equiv.swap (0 : Fin 2) 1)) *
      blockPow f n g 2 =
    blockPow f n g 2 *
      permClass f (n * 2)
        (blockPerm n (Equiv.swap (0 : Fin 2) 1)) := by
  suffices h : endCast f (Nat.mul_add n 1 1)
      (permClass f (n * 2)
          (blockPerm n (Equiv.swap (0 : Fin 2) 1)) *
        blockPow f n g 2) =
    endCast f (Nat.mul_add n 1 1)
      (blockPow f n g 2 *
        permClass f (n * 2)
          (blockPerm n (Equiv.swap (0 : Fin 2) 1))) by
    have := congrArg (endCast f (Nat.mul_add n 1 1).symm) h
    rwa [endCast_trans, endCast_rfl,
      endCast_trans, endCast_rfl] at this
  rw [endCast_mul, endCast_mul,
    endCast_permClass f (Nat.mul_add n 1 1),
    blockPerm_swap01_eq_transposeEquiv,
    show endCast f (Nat.mul_add n 1 1) (blockPow f n g 2) =
      blockTensorEnd f (blockPow f n g 1)
        (blockPow f n g 1) from blockPow_split f n g 1 1]
  exact blockSwap01_comm f (n * 1) (blockPow f n g 1)

-- Raised budget: the induction on the block count carries the
-- permutation class and the block power at every step.
/-- Adjacent swap commutes with blockPow (by induction on k). -/
private theorem block_adj_swap_comm (k : ℕ) (i : ℕ)
    (hi : i + 2 ≤ k) (g : skeinEnd f n) :
    permClass f (n * k) (blockPerm n
      (Equiv.swap (⟨i, by omega⟩ : Fin k)
        ⟨i + 1, by omega⟩)) *
      blockPow f n g k =
    blockPow f n g k *
      permClass f (n * k) (blockPerm n
        (Equiv.swap (⟨i, by omega⟩ : Fin k)
          ⟨i + 1, by omega⟩)) := by
  induction k with
  | zero => omega
  | succ k' ihk =>
      cases k' with
      | zero => omega
      | succ k'' =>
          -- k = k'' + 2
          by_cases hi' : i + 2 ≤ k'' + 1
          · -- Internal: swap doesn't touch last position
            rw [swap_internal_block' i hi']
            set σ' := Equiv.swap
              (⟨i, by omega⟩ : Fin (k'' + 1))
              ⟨i + 1, by omega⟩
            -- Decompose at arity n * (k'' + 1) + n * 1
            have hperm : permClass f (n * (k'' + 2))
                (blockPerm n
                  ((@finSumFinEquiv (k'' + 1) 1).permCongr
                    (Equiv.sumCongr σ'
                      (1 : Equiv.Perm (Fin 1))))) =
              endCast f (Nat.mul_add n (k'' + 1) 1).symm
                (blockTensorEnd f
                  (permClass f (n * (k'' + 1))
                    (blockPerm n σ'))
                  (1 : skeinEnd f (n * 1))) := by
              have h1 := endCast_permClass f
                (Nat.mul_add n (k'' + 1) 1)
                (blockPerm n
                  ((@finSumFinEquiv (k'' + 1) 1).permCongr
                    (Equiv.sumCongr σ'
                      (1 : Equiv.Perm (Fin 1)))))
              rw [blockPerm_sumCongr, blockPerm_one,
                permClass_blockTensorEnd,
                show permClass f (n * 1)
                    (1 : Equiv.Perm (Fin (n * 1))) =
                  (1 : skeinEnd f (n * 1)) from
                  map_one (permToEnd f (n * 1))] at h1
              have h2 := congrArg
                (endCast f
                  (Nat.mul_add n (k'' + 1) 1).symm) h1
              rw [endCast_trans, endCast_rfl] at h2
              exact h2
            have hpow : blockPow f n g (k'' + 2) =
              endCast f (Nat.mul_add n (k'' + 1) 1).symm
                (blockTensorEnd f
                  (blockPow f n g (k'' + 1))
                  (blockPow f n g 1)) := by
              have h3 := blockPow_split f n g (k'' + 1) 1
              have h4 := congrArg
                (endCast f
                  (Nat.mul_add n (k'' + 1) 1).symm) h3
              rw [endCast_trans, endCast_rfl] at h4
              exact h4
            rw [hperm, hpow, ← endCast_mul, ← endCast_mul]
            congr 1
            exact blockTensorEnd_comm f _ _ _ _
              (ihk (by omega))
              ((one_mul _).trans (mul_one _).symm)
          · -- Last: i = k'', swap of last two positions
            have him : i = k'' := by omega
            subst him
            -- After subst, k'' is eliminated; use i everywhere
            rw [swap_last_block' i]
            -- Decompose at arity n * i + n * 2
            have hperm : permClass f (n * (i + 2))
                (blockPerm n (finSumFinEquiv.permCongr
                  (Equiv.sumCongr 1
                    (Equiv.swap (0 : Fin 2) 1)))) =
              endCast f (Nat.mul_add n i 2).symm
                (blockTensorEnd f
                  (1 : skeinEnd f (n * i))
                  (permClass f (n * 2)
                    (blockPerm n
                      (Equiv.swap (0 : Fin 2) 1)))) := by
              have h1 := endCast_permClass f
                (Nat.mul_add n i 2)
                (blockPerm n (finSumFinEquiv.permCongr
                  (Equiv.sumCongr 1
                    (Equiv.swap (0 : Fin 2) 1))))
              rw [blockPerm_sumCongr, blockPerm_one,
                permClass_blockTensorEnd,
                show permClass f (n * i)
                    (1 : Equiv.Perm (Fin (n * i))) =
                  (1 : skeinEnd f (n * i)) from
                  map_one (permToEnd f _)] at h1
              have h2 := congrArg
                (endCast f (Nat.mul_add n i 2).symm) h1
              rw [endCast_trans, endCast_rfl] at h2
              exact h2
            have hpow : blockPow f n g (i + 2) =
              endCast f (Nat.mul_add n i 2).symm
                (blockTensorEnd f
                  (blockPow f n g i)
                  (blockPow f n g 2)) := by
              have h3 := blockPow_split f n g i 2
              have h4 := congrArg
                (endCast f (Nat.mul_add n i 2).symm) h3
              rw [endCast_trans, endCast_rfl] at h4
              exact h4
            rw [hperm, hpow, ← endCast_mul, ← endCast_mul]
            congr 1
            exact blockTensorEnd_comm f _ _ _ _
              ((one_mul _).trans (mul_one _).symm)
              (swap01_comm_blockPow2 f g)

/-- Any transposition commutes with blockPow
    (induction on the distance `|y - x|`). -/
private theorem block_swap_comm (x y : Fin k)
    (hxy : x ≠ y) (g : skeinEnd f n) :
    permClass f (n * k) (blockPerm n (Equiv.swap x y)) *
      blockPow f n g k =
    blockPow f n g k *
      permClass f (n * k)
        (blockPerm n (Equiv.swap x y)) := by
  suffices key : ∀ (d : ℕ) (x y : Fin k),
      x ≠ y → x.val < y.val →
        y.val - x.val = d + 1 →
      permClass f (n * k)
          (blockPerm n (Equiv.swap x y)) *
        blockPow f n g k =
      blockPow f n g k *
        permClass f (n * k)
          (blockPerm n (Equiv.swap x y)) by
    rcases Nat.lt_or_gt_of_ne
        (Fin.val_ne_of_ne hxy) with hlt | hgt
    · exact key (y.val - x.val - 1) x y hxy hlt
        (by omega)
    · rw [Equiv.swap_comm]
      exact key (x.val - y.val - 1) y x (Ne.symm hxy)
        hgt (by omega)
  have pmul : ∀ (a b : Equiv.Perm (Fin k)),
      permClass f (n * k) (blockPerm n (a * b)) =
        permClass f (n * k) (blockPerm n a) *
          permClass f (n * k) (blockPerm n b) := by
    intro a b
    rw [blockPerm_mul]
    exact map_mul (permToEnd f (n * k)) _ _
  intro d
  induction d with
  | zero =>
      intro x y _ hlt hd
      have hyk : y.val < k := y.isLt
      have heq : y = ⟨x.val + 1, by omega⟩ :=
        Fin.ext (by simp only []; omega)
      rw [heq]
      exact block_adj_swap_comm f k x.val (by omega) g
  | succ d' ih =>
      intro x y hxy hlt hd
      have hyk : y.val < k := y.isLt
      have hx1_lt : x.val + 1 < k := by omega
      set x1 : Fin k := ⟨x.val + 1, hx1_lt⟩
      have hx_ne_x1 : x ≠ x1 :=
        Fin.ne_of_val_ne (by simp only [x1]; omega)
      have hx1_ne_y : x1 ≠ y :=
        Fin.ne_of_val_ne (by simp only [x1]; omega)
      have decomp : Equiv.swap x y =
          Equiv.swap x x1 * Equiv.swap x1 y *
            Equiv.swap x x1 := by
        have := Equiv.swap_mul_swap_mul_swap
          hx1_ne_y.symm hxy.symm
        rw [Equiv.swap_comm x1 x,
          Equiv.swap_comm y x1] at this
        exact this.symm
      have adj : permClass f (n * k)
          (blockPerm n (Equiv.swap x x1)) *
            blockPow f n g k =
          blockPow f n g k *
            permClass f (n * k)
              (blockPerm n (Equiv.swap x x1)) :=
        block_adj_swap_comm f k x.val (by omega) g
      have inner : permClass f (n * k)
          (blockPerm n (Equiv.swap x1 y)) *
            blockPow f n g k =
          blockPow f n g k *
            permClass f (n * k)
              (blockPerm n (Equiv.swap x1 y)) :=
        ih x1 y hx1_ne_y
          (by simp only [x1]; omega)
          (by simp only [x1]; omega)
      rw [decomp, pmul, pmul]
      set A := permClass f (n * k)
        (blockPerm n (Equiv.swap x x1))
      set B := permClass f (n * k)
        (blockPerm n (Equiv.swap x1 y))
      set G := blockPow f n g k
      calc ((A * B) * A) * G
          = (A * B) * (A * G) := by rw [mul_assoc]
        _ = (A * B) * (G * A) := by rw [adj]
        _ = A * (B * (G * A)) := by rw [mul_assoc]
        _ = A * ((B * G) * A) := by
              rw [← mul_assoc B G A]
        _ = A * ((G * B) * A) := by rw [inner]
        _ = A * (G * (B * A)) := by
              rw [mul_assoc G B A]
        _ = (A * G) * (B * A) := by
              rw [← mul_assoc A G _]
        _ = (G * A) * (B * A) := by rw [adj]
        _ = G * (A * (B * A)) := by rw [mul_assoc]
        _ = G * ((A * B) * A) := by
              rw [← mul_assoc A B A]

/-! ### The block cycle trace -/

/-- **The block cycle trace**: closing the block rotation against
`c` diagonal blocks is the trace of the `c`-th power, via the block
splice. -/
theorem skeinTrace_blockCycle (n : ℕ) (g : skeinEnd f n)
    (c : ℕ) :
    skeinTrace f (n * (c + 1))
      (permClass f (n * (c + 1))
          (blockPerm n (finRotate (c + 1))) *
        blockPow f n g (c + 1)) =
    skeinTrace f n (g ^ (c + 1)) :=
  skeinTrace_blockCycle' f n g c

/-- Block permutations commute with the block-diagonal power. -/
theorem blockPerm_mul_blockPow_comm (n : ℕ) {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (g : skeinEnd f n) :
    permClass f (n * k) (blockPerm n σ) * blockPow f n g k =
      blockPow f n g k *
        permClass f (n * k) (blockPerm n σ) := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
      rw [blockPerm_one, show permClass f (n * k)
        (1 : Equiv.Perm (Fin (n * k))) =
        (1 : skeinEnd f (n * k)) from map_one (permToEnd f _),
        one_mul, mul_one]
  | swap_mul τ x y hxy ih =>
      rw [blockPerm_mul,
        show permClass f (n * k) (blockPerm n (Equiv.swap x y) *
          blockPerm n τ) =
          permClass f (n * k) (blockPerm n (Equiv.swap x y)) *
            permClass f (n * k) (blockPerm n τ) from
          map_mul (permToEnd f _) _ _,
        mul_assoc, ih, ← mul_assoc]
      rw [block_swap_comm f x y hxy g, mul_assoc]

/-- **Block factorization over the block-cycle normal form.** -/
theorem skeinTrace_blockCycles_mul_pow (n : ℕ)
    (l : List ℕ) (hl : ∀ c ∈ l, 1 ≤ c) (g : skeinEnd f n) :
    skeinTrace f (n * l.sum)
      (permClass f (n * l.sum)
          (blockPerm n (blockCycles l)) *
        blockPow f n g l.sum) =
    (l.map (fun c => skeinTrace f n (g ^ c))).prod := by
  induction l with
  | nil =>
      rw [show (blockCycles ([] : List ℕ)) =
            (1 : Equiv.Perm (Fin ([] : List ℕ).sum)) from rfl,
        blockPerm_one,
        show permClass f (n * ([] : List ℕ).sum)
            (1 : Equiv.Perm (Fin (n * ([] : List ℕ).sum))) =
          (1 : skeinEnd f (n * ([] : List ℕ).sum))
          from map_one (permToEnd f _),
        show blockPow f n g ([] : List ℕ).sum =
          (1 : skeinEnd f (n * ([] : List ℕ).sum)) from rfl,
        one_mul, List.map_nil, List.prod_nil]
      exact skeinTrace_zero_one f
  | cons c rest ih =>
      have hc : 1 ≤ c := hl c List.mem_cons_self
      have hrest : ∀ x ∈ rest, 1 ≤ x := fun x hx =>
        hl x (List.mem_cons_of_mem c hx)
      set S := rest.sum with hS_def
      show skeinTrace f (n * (c + S))
          (permClass f (n * (c + S))
              (blockPerm n (blockCycles (c :: rest))) *
            blockPow f n g (c + S)) =
        skeinTrace f n (g ^ c) *
          (rest.map (fun x => skeinTrace f n (g ^ x))).prod
      rw [show (blockCycles (c :: rest) :
              Equiv.Perm (Fin (c + S))) =
            finSumFinEquiv.permCongr (Equiv.sumCongr
              (finRotate c) (blockCycles rest)) from rfl]
      -- Decompose permClass via blockPerm_sumCongr
      set H := Nat.mul_add n c S with hH_def
      have hperm : permClass f (n * (c + S))
          (blockPerm n (finSumFinEquiv.permCongr
            (Equiv.sumCongr (finRotate c)
              (blockCycles rest)))) =
        endCast f H.symm (blockTensorEnd f
          (permClass f (n * c) (blockPerm n (finRotate c)))
          (permClass f (n * S)
            (blockPerm n (blockCycles rest)))) := by
        have h1 := endCast_permClass f H
          (blockPerm n (finSumFinEquiv.permCongr
            (Equiv.sumCongr (finRotate c)
              (blockCycles rest))))
        rw [blockPerm_sumCongr, permClass_blockTensorEnd] at h1
        have h2 := congrArg (endCast f H.symm) h1
        rw [endCast_trans, endCast_rfl] at h2
        exact h2
      rw [hperm]
      -- Decompose blockPow via blockPow_split
      have hpow : blockPow f n g (c + S) =
        endCast f H.symm (blockTensorEnd f
          (blockPow f n g c) (blockPow f n g S)) := by
        have h3 := blockPow_split f n g c S
        have h4 := congrArg (endCast f H.symm) h3
        rw [endCast_trans, endCast_rfl] at h4
        exact h4
      rw [hpow, ← endCast_mul, blockTensorEnd_mul,
        skeinTrace_endCast, skeinTrace_blockTensorEnd,
        ih hrest]
      -- First factor is skeinTrace_blockCycle
      cases c with
      | zero => omega
      | succ c' =>
          rw [skeinTrace_blockCycle]

/-- **The block trace factorization**: the trace of a block
permutation against the block-diagonal power is the cycle-type
product of block power traces, fixed points included. -/
theorem skeinTrace_blockPerm_mul_pow (n : ℕ) {k : ℕ}
    (π : Equiv.Perm (Fin k)) (g : skeinEnd f n) :
    skeinTrace f (n * k)
        (permClass f (n * k) (blockPerm n π) *
          blockPow f n g k) =
      (π.cycleType.map
          (fun c => skeinTrace f n (g ^ c))).prod *
        (skeinTrace f n (g ^ 1)) ^ (k - π.cycleType.sum) := by
  obtain ⟨l, h, σ, hl, hcoe, hσ⟩ := exists_conj_blockCycles π
  subst h
  have hB : (finCongr (rfl : l.sum = l.sum)).permCongr
      (blockCycles l) = blockCycles l := by
    ext x
    simp
  rw [hB] at hσ
  have hconj : blockPerm n π =
      blockPerm n σ * blockPerm n (blockCycles l) *
        blockPerm n σ⁻¹ := by
    rw [← blockPerm_mul, ← blockPerm_mul, hσ]
  rw [hconj]
  have permClass_mul : ∀ a b : Equiv.Perm (Fin (n * l.sum)),
      permClass f (n * l.sum) (a * b) =
        permClass f (n * l.sum) a *
          permClass f (n * l.sum) b :=
    fun a b => map_mul (permToEnd f (n * l.sum)) a b
  conv_lhs => rw [permClass_mul, permClass_mul]
  rw [mul_assoc (permClass f (n * l.sum) (blockPerm n σ) *
    permClass f (n * l.sum) (blockPerm n (blockCycles l)))]
  rw [blockPerm_mul_blockPow_comm]
  rw [← mul_assoc,
    mul_assoc (permClass f (n * l.sum) (blockPerm n σ))]
  have hσinv : permClass f (n * l.sum) (blockPerm n σ⁻¹) =
      permClass f (n * l.sum) ((blockPerm n σ)⁻¹) := by
    rw [show blockPerm n σ⁻¹ = (blockPerm n σ)⁻¹ from
      map_inv (blockPermHom n l.sum) σ]
  rw [hσinv, skeinTrace_conj']
  rw [skeinTrace_blockCycles_mul_pow f n l hl]
  have hsplit : (l : Multiset ℕ) = π.cycleType +
      Multiset.replicate (l.sum - π.cycleType.sum) 1 := by
    rw [hcoe, fullCycleType]
  calc (l.map (fun c => skeinTrace f n (g ^ c))).prod
      = (((l : Multiset ℕ)).map
          (fun c => skeinTrace f n (g ^ c))).prod := by
        rw [Multiset.map_coe, Multiset.prod_coe]
    _ = _ := by
        rw [hsplit, Multiset.map_add, Multiset.prod_add,
          Multiset.map_replicate, Multiset.prod_replicate]

end RS
