/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Envelope.SkeinTower
public import LeanPool.RegtsSevenster.RS.Novel.Skein.MonoidalInstance

/-!
# The block tower

The symmetric group `S_k` acting by block permutations on `n·k`
strands: the permutation representation, the block-diagonal tensor
power, and the `PermTower` structure at the `n`-strand ambient —
the scaffolding for nilpotent-trace vanishing at every arity.

The step arithmetic is definitional: `n * (k + 1) ≡ n * k + n`,
so the recursive block constructions live at the same indices as
the tensor structure.
-/

@[expose] public section

namespace RS

open CategoryTheory

/-! ### Block permutations -/

/-- The block permutation: `σ : S_k` acting on `k` contiguous
blocks of `n` strands. -/
noncomputable def blockPerm (n : ℕ) {k : ℕ}
    (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (n * k)) :=
  (finCongr (Nat.mul_comm k n)).permCongr
    ((finProdFinEquiv (m := k) (n := n)).permCongr
      (Equiv.prodCongr σ (Equiv.refl (Fin n))))

/-- Block permutation of the identity. -/
theorem blockPerm_one (n k : ℕ) :
    blockPerm n (1 : Equiv.Perm (Fin k)) = 1 := by
  ext x
  simp [blockPerm, Nat.mod_add_div]

/-- Block permutations are multiplicative. -/
theorem blockPerm_mul (n : ℕ) {k : ℕ}
    (σ τ : Equiv.Perm (Fin k)) :
    blockPerm n (σ * τ) = blockPerm n σ * blockPerm n τ := by
  ext x
  simp [blockPerm]

/-- The block-permutation monoid homomorphism. -/
noncomputable def blockPermHom (n k : ℕ) :
    Equiv.Perm (Fin k) →* Equiv.Perm (Fin (n * k)) where
  toFun := blockPerm n
  map_one' := blockPerm_one n k
  map_mul' := blockPerm_mul n

/-- The value of a block permutation on `n·q + r`. -/
theorem blockPerm_val (n : ℕ) {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (q : Fin k) (r : Fin n) :
    blockPerm n σ
        ⟨n * q.val + r.val, by
          have hq := q.isLt
          have hr := r.isLt
          calc n * q.val + r.val < n * q.val + n := by omega
            _ = n * (q.val + 1) := by ring
            _ ≤ n * k := Nat.mul_le_mul_left n (by omega)⟩ =
      ⟨n * (σ q).val + r.val, by
        have hq := (σ q).isLt
        have hr := r.isLt
        calc n * (σ q).val + r.val < n * (σ q).val + n := by
              omega
          _ = n * ((σ q).val + 1) := by ring
          _ ≤ n * k := Nat.mul_le_mul_left n (by omega)⟩ := by
  have hn : 0 < n := by
    have := r.isLt
    omega
  have hmod : (n * q.val + r.val) % n = r.val := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt r.isLt]
  have hdiv : (n * q.val + r.val) / n = q.val := by
    rw [Nat.mul_add_div hn, Nat.div_eq_of_lt r.isLt]
    omega
  apply Fin.ext
  simp only [blockPerm, Equiv.permCongr_apply, finCongr_apply,
    Equiv.prodCongr_apply, finProdFinEquiv, Equiv.coe_fn_mk,
    Equiv.coe_fn_symm_mk, Fin.val_cast]
  simp [Fin.modNat, Fin.divNat, hmod, hdiv]
  ring

/-! ### The block representation -/

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The block representation of the group algebra of `S_k` on
`n·k` strands. -/
noncomputable def blockRep (n k : ℕ) :
    SymGroupAlgebra k →ₐ[ℂ] skeinEnd f (n * k) :=
  MonoidAlgebra.lift ℂ (skeinEnd f (n * k))
    (Equiv.Perm (Fin k))
    ((permToEnd f (n * k)).comp (blockPermHom n k))

/-- `blockRep` on a single permutation. -/
theorem blockRep_of (n k : ℕ) (σ : Equiv.Perm (Fin k)) :
    blockRep f n k
        (MonoidAlgebra.of ℂ (Equiv.Perm (Fin k)) σ) =
      permClass f (n * k) (blockPerm n σ) :=
  MonoidAlgebra.lift_of _ σ

/-! ### The block-diagonal power -/

/-- The End-typed tensor at block arities. -/
noncomputable def blockTensorEnd {a b : ℕ}
    (u : skeinEnd f a) (v : skeinEnd f b) :
    skeinEnd f (a + b) :=
  (MonoidalCategoryStruct.tensorHom
      (X₁ := SkeinObj.mk a) (Y₁ := SkeinObj.mk a)
      (X₂ := SkeinObj.mk b) (Y₂ := SkeinObj.mk b) u v :
    End (SkeinObj.mk (a + b)))

/-- The block-diagonal tensor power: `k` copies of an `n`-strand
endomorphism.  The index arithmetic is definitional:
`n * (k + 1) ≡ n * k + n`. -/
noncomputable def blockPow (n : ℕ) (g : skeinEnd f n) :
    (k : ℕ) → skeinEnd f (n * k)
  | 0 => 1
  | k + 1 => blockTensorEnd f (blockPow n g k) g

/-! ### The block permutation tower -/

/-- The dimension bound at block arities:
`R ^ (2·n·k) = (R ^ n) ^ (2·k)`. -/
theorem blockEnd_finrank_le (n k : ℕ) :
    Module.finrank ℂ (skeinEnd f (n * k)) ≤
      (R ^ n) ^ (2 * k) := by
  calc Module.finrank ℂ (skeinEnd f (n * k)) ≤
      R ^ (2 * (n * k)) := skeinEnd_finrank_le f (n * k)
    _ = (R ^ n) ^ (2 * k) := by
      rw [← pow_mul]
      ring_nf

/-- The block permutation of an extended permutation is the
extension of the block permutation. -/
private theorem blockPerm_viaEmbedding (n : ℕ) {j k : ℕ}
    (h : j ≤ k) (σ : Equiv.Perm (Fin j)) :
    blockPerm n
        (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ) =
      Equiv.Perm.viaEmbeddingHom
        (Fin.castLEEmb (Nat.mul_le_mul_left n h))
        (blockPerm n σ) := by
  by_cases hn : n = 0
  · subst hn; ext ⟨v, hv⟩; simp at hv
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    ext ⟨v, hv⟩
    -- Decompose v = n * q + r
    have hqk : v / n < k := Nat.div_lt_of_lt_mul (by omega)
    have hrn : v % n < n := Nat.mod_lt _ hn'
    have hv_decomp : v = n * (v / n) + v % n :=
      (Nat.div_add_mod v n).symm
    -- Compute LHS value via blockPerm_val
    set τ := Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ
    have hLHS := blockPerm_val n τ ⟨v / n, hqk⟩ ⟨v % n, hrn⟩
    have hv_bound : n * (v / n) + v % n < n * k := hv_decomp ▸ hv
    have hv_fin : (⟨v, hv⟩ : Fin (n * k)) =
        ⟨n * (v / n) + v % n, hv_bound⟩ := Fin.ext hv_decomp
    conv_lhs => rw [hv_fin]
    rw [hLHS]
    by_cases hqj : v / n < j
    · -- v / n < j: in-range, both sides apply σ
      -- Simplify τ on q
      have hτq : (τ ⟨v / n, hqk⟩).val = (σ ⟨v / n, hqj⟩).val := by
        change (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ
          ⟨v / n, hqk⟩).val = _
        rw [Equiv.Perm.viaEmbeddingHom_apply,
          show (⟨v / n, hqk⟩ : Fin k) =
            Fin.castLEEmb h ⟨v / n, hqj⟩ from Fin.ext rfl,
          Equiv.Perm.viaEmbedding_apply]
        simp [Fin.castLEEmb]
      -- Simplify RHS via viaEmbedding_apply + blockPerm_val
      have hv_lt : v < n * j := by
        calc v = n * (v / n) + v % n := hv_decomp
          _ < n * (v / n) + n := by omega
          _ = n * (v / n + 1) := by ring
          _ ≤ n * j := Nat.mul_le_mul_left n (by omega)
      conv_rhs =>
        rw [Equiv.Perm.viaEmbeddingHom_apply,
          show (⟨v, hv⟩ : Fin (n * k)) =
            Fin.castLEEmb (Nat.mul_le_mul_left n h)
              ⟨v, hv_lt⟩ from Fin.ext rfl,
          Equiv.Perm.viaEmbedding_apply]
      have hbp := blockPerm_val n σ ⟨v / n, hqj⟩ ⟨v % n, hrn⟩
      have hv_bound' : n * (v / n) + v % n < n * j :=
        hv_decomp ▸ hv_lt
      have hv_fin' : (⟨v, hv_lt⟩ : Fin (n * j)) =
          ⟨n * (v / n) + v % n, hv_bound'⟩ := Fin.ext hv_decomp
      conv_rhs => rw [hv_fin', hbp]
      simp only [Fin.castLEEmb, hτq]
      rfl
    · -- v / n ≥ j: both sides fix the element
      push Not at hqj
      have hv_ge : n * j ≤ v := by
        calc n * j ≤ n * (v / n) := Nat.mul_le_mul_left n hqj
          _ ≤ n * (v / n) + v % n := Nat.le_add_right _ _
          _ = v := Nat.div_add_mod v n
      -- LHS: τ fixes q
      have hτq : (τ ⟨v / n, hqk⟩).val = v / n := by
        change (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ
          ⟨v / n, hqk⟩).val = _
        rw [Equiv.Perm.viaEmbeddingHom_apply,
          Equiv.Perm.viaEmbedding_apply_of_notMem σ
            (Fin.castLEEmb h) ⟨v / n, hqk⟩
            (fun ⟨a, ha⟩ => by
              have := congrArg Fin.val ha
              simp [Fin.castLEEmb] at this; omega)]
      -- RHS: viaEmbeddingHom fixes the element
      conv_rhs =>
        rw [Equiv.Perm.viaEmbeddingHom_apply,
          Equiv.Perm.viaEmbedding_apply_of_notMem
            (blockPerm n σ)
            (Fin.castLEEmb (Nat.mul_le_mul_left n h))
            ⟨v, hv⟩ (fun ⟨a, ha⟩ => by
              have := congrArg Fin.val ha
              simp [Fin.castLEEmb] at this
              have := a.isLt; omega)]
      have goal_eq : n * (τ ⟨v / n, hqk⟩).val + v % n = v := by
        rw [hτq]; exact Nat.div_add_mod v n
      exact goal_eq

/-- Vanishing propagates along the standard embeddings of block
representations. -/
theorem blockRep_compat (n : ℕ) {j k : ℕ} (h : j ≤ k)
    (x : SymGroupAlgebra j) :
    blockRep f n j x = 0 →
      blockRep f n k (symCast h x) = 0 := by
  intro hx
  have h' : n * j ≤ n * k := Nat.mul_le_mul_left n h
  -- Factor blockRep through skeinRep via blockPermHom
  -- blockRep f n m y = skeinRep f (n*m) (mapDomainAlgHom (blockPermHom n m) y)
  -- naturality: mapDomain (blockPermHom n k) ∘ symCast = symCast h' ∘ mapDomain
  --   (blockPermHom n j)
  let bLift := fun m => MonoidAlgebra.mapDomainAlgHom ℂ ℂ
    (blockPermHom n m)
  -- Step 1: blockRep factors through skeinRep
  have hfactor : ∀ (m : ℕ) (y : SymGroupAlgebra m),
      blockRep f n m y =
        skeinRep f (n * m) (bLift m y) := by
    intro m y
    apply MonoidAlgebra.induction_on y
    · intro σ
      rw [blockRep_of]
      change permClass f (n * m) (blockPerm n σ) =
        skeinRep f (n * m)
          (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockPermHom n m)
            (MonoidAlgebra.of ℂ _ σ))
      rw [show MonoidAlgebra.mapDomainAlgHom ℂ ℂ
            (blockPermHom n m)
            (MonoidAlgebra.of ℂ (Equiv.Perm (Fin m)) σ) =
          MonoidAlgebra.of ℂ (Equiv.Perm (Fin (n * m)))
            (blockPerm n σ) from by
        change MonoidAlgebra.mapDomain (blockPermHom n m)
            (MonoidAlgebra.single σ 1) =
          MonoidAlgebra.single (blockPerm n σ) 1
        exact MonoidAlgebra.mapDomain_single,
        skeinRep_of]
    · intro a b ha hb
      simp only [map_add, ha, hb]
    · intro c z hz
      simp only [map_smul, hz]
  -- Step 2: bLift commutes with symCast (naturality)
  have hnat : ∀ (y : SymGroupAlgebra j),
      bLift k (symCast h y) = symCast h' (bLift j y) := by
    intro y
    apply MonoidAlgebra.induction_on y
    · intro σ
      show bLift k (symCast h (MonoidAlgebra.of ℂ _ σ)) =
        symCast h' (bLift j (MonoidAlgebra.of ℂ _ σ))
      -- LHS: bLift k (of (viaEmbeddingHom (castLEEmb h) σ))
      --    = of (blockPerm n (viaEmbeddingHom (castLEEmb h) σ))
      change MonoidAlgebra.mapDomain (blockPermHom n k)
          (MonoidAlgebra.mapDomain
            (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h))
            (MonoidAlgebra.single σ 1)) =
        MonoidAlgebra.mapDomain
          (Equiv.Perm.viaEmbeddingHom
            (Fin.castLEEmb h'))
          (MonoidAlgebra.mapDomain (blockPermHom n j)
            (MonoidAlgebra.single σ 1))
      rw [MonoidAlgebra.mapDomain_single,
        MonoidAlgebra.mapDomain_single,
        MonoidAlgebra.mapDomain_single,
        MonoidAlgebra.mapDomain_single]
      congr 1
      exact blockPerm_viaEmbedding n h σ
    · intro a b ha hb
      simp only [map_add, ha, hb]
    · intro c z hz
      simp only [map_smul, hz]
  -- Conclude
  rw [hfactor k (symCast h x), hnat x]
  exact skeinRep_compat f h' (bLift j x) (by rwa [← hfactor])

/-- **The block permutation tower**: `S_k` acting by block
permutations on the `n·k`-strand endomorphism algebras, of growth
`(R ^ n) ^ 2`. -/
noncomputable def blockPermTower (n : ℕ) :
    PermTower (fun k => skeinEnd f (n * k)) (((R : ℝ) ^ n) ^ 2) where
  rep k := blockRep f n k
  compat h x hx := blockRep_compat f n h x hx
  bound k := by
    have h : ((Module.finrank ℂ (skeinEnd f (n * k)) : ℕ) : ℝ)
        ≤ (((R ^ n) ^ (2 * k) : ℕ) : ℝ) := by
      exact_mod_cast blockEnd_finrank_le f n k
    calc ((Module.finrank ℂ (skeinEnd f (n * k)) : ℕ) : ℝ)
        ≤ (((R ^ n) ^ (2 * k) : ℕ) : ℝ) := h
      _ = (((R : ℝ) ^ n) ^ 2) ^ k := by
          push_cast
          rw [← pow_mul, ← pow_mul, ← pow_mul]

end RS
