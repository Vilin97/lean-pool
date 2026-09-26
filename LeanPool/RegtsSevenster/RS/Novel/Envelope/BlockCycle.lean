/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Envelope.BlockSplice
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.Frobenius
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.BlockTower

/-!
# The block cycle trace

Closing a block rotation against `c + 1` diagonal copies of `g`
gives the trace of `g ^ (c + 1)`: the rotation carries each copy
onto the next, and after `c + 1` turns the copies have composed.

The rotation by one block is `blockPerm n (finRotate (c+1))`, which
is `blockRot (n*c) n`; the splice `partialCloseBlockSplice` peels
one block off it, first at fragments and then at trace values.  An
induction on the number of blocks then turns the tensor of a tuple
into the tuple's cyclic composite, which for a constant tuple is a
power.
-/

@[expose] public section

namespace RS

open CategoryTheory

variable {R : ℕ} (f : EdgeRankParameter R)

/-! ### The rotation by one block -/

/-- Forward value of `finRotate`. -/
private theorem finRotate_val' (c : ℕ) (q : Fin (c + 1)) :
    (finRotate (c + 1) q).val = if q.val = c then 0 else q.val + 1 := by
  have h := congrArg Fin.val (finRotate_apply q)
  rw [Fin.val_add_one] at h
  rw [h]
  by_cases hq : q.val = c
  · rw [ite_eq_left (Fin.ext hq : q = Fin.last c), ite_eq_left hq]
  · rw [ite_eq_right (show q ≠ Fin.last c from fun h =>
      hq (congrArg Fin.val h)), ite_eq_right hq]

/-- `blockPerm n (finRotate (c+1))` equals `blockRot (n*c) n`:
both rotate strands by n modulo n*(c+1). -/
theorem blockPerm_finRotate_eq_blockRot (n c : ℕ) :
    blockPerm n (finRotate (c + 1)) = blockRot (n * c) n := by
  by_cases hn : n = 0
  · subst hn; ext x; exact absurd x.isLt (by omega)
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    ext x : 1
    apply Fin.ext
    -- Decompose x = n * q + r
    set q := x.val / n
    set r := x.val % n
    have hx_eq : x.val = n * q + r := (Nat.div_add_mod x.val n).symm
    have hq_lt : q < c + 1 := by
      apply Nat.div_lt_of_lt_mul
      show x.val < n * (c + 1)
      exact x.isLt
    have hr_lt : r < n := Nat.mod_lt _ hn'
    -- LHS: blockPerm_val
    have hbp := congrArg Fin.val
      (blockPerm_val n (finRotate (c + 1)) ⟨q, hq_lt⟩ ⟨r, hr_lt⟩)
    -- RHS: blockRot_val'
    have hbr := blockRot_val (n * c) n x
    -- Reconstruct x as ⟨n * q + r, _⟩
    have hx_mk : x = ⟨n * q + r, by rw [← hx_eq]; exact x.isLt⟩ :=
      Fin.ext hx_eq
    -- Compute both sides' values
    have lhs_val : (blockPerm n (finRotate (c + 1)) x).val =
        n * (finRotate (c + 1) ⟨q, hq_lt⟩).val + r := by
      conv_lhs => rw [hx_mk]
      exact hbp
    have rhs_val : (blockRot (n * c) n x).val =
        if n * q + r < n * c then n + (n * q + r)
        else n * q + r - (n * c) := by
      rw [hbr, hx_eq]
    rw [lhs_val, rhs_val, finRotate_val' c ⟨q, hq_lt⟩]
    by_cases hqc : q = c
    · -- q = c: finRotate wraps, blockRot wraps
      rw [ite_eq_left hqc, hqc, ite_eq_right (by omega),
        show n * (0 : ℕ) = 0 from mul_zero n, zero_add]
      omega
    · -- q ≠ c: finRotate shifts, blockRot shifts
      have hqc' : q + 1 ≤ c := by omega
      rw [ite_eq_right hqc,
        ite_eq_left (show n * q + r < n * c from
          by nlinarith [Nat.mul_le_mul_left n hqc'])]
      ring

/-! ### Trace and interchange for the block tensor -/

/-- Trace of a block tensor product. -/
theorem skeinTrace_blockTensorEnd {a b : ℕ}
    (u : skeinEnd f a) (v : skeinEnd f b) :
    skeinTrace f (a + b) (blockTensorEnd f u v) =
      skeinTrace f a u * skeinTrace f b v :=
  skeinTrace_tensorHom f u v

/-- Interchange law for blockTensorEnd multiplication. -/
theorem blockTensorEnd_mul {a b : ℕ}
    (u₁ u₂ : skeinEnd f a) (v₁ v₂ : skeinEnd f b) :
    blockTensorEnd f u₁ v₁ * blockTensorEnd f u₂ v₂ =
      blockTensorEnd f (u₁ * u₂) (v₁ * v₂) :=
  MonoidalCategory.tensorHom_comp_tensorHom
    (u₂ : SkeinObj.mk (f := f) a ⟶ SkeinObj.mk a)
    (v₂ : SkeinObj.mk (f := f) b ⟶ SkeinObj.mk b)
    (u₁ : SkeinObj.mk (f := f) a ⟶ SkeinObj.mk a)
    (v₁ : SkeinObj.mk (f := f) b ⟶ SkeinObj.mk b)

/-! ### The rotation step at fragments -/

-- Five fragment equivalences are chained on each
-- side of the closure before the splice applies.
/-- Core fragment-level identity for the block rotation step:
the trace of a rotated tensor equals the trace of the spliced
composite at one lower block arity. -/
private theorem fragTrace_block_rot_step_core (K n : ℕ)
    (𝔄 : Fragment (Fin ((K + n) + (K + n))))
    (𝔊 : Fragment (Fin (n + n))) :
    fragTrace f.val
      ((tensorFragment 𝔄 𝔊).compose
        (permFragment (blockRot (K + n) n))) =
    fragTrace f.val
      ((𝔄.compose (tensorFragment (strandBundle K) 𝔊)).compose
        (permFragment (blockRot K n))) := by
  -- E_L: decompose the LHS closure
  have E1 := pairCloseCongr
    (composePermFragment (s := (K + n) + n) (t := (K + n) + n)
      (blockRot (K + n) n)
      (tensorFragment 𝔄 𝔊))
    (Fragment.Equiv.refl (strandBundle (K + n + n)))
  have E2 := pairCloseRelabelPerm
    (outPermEquiv (K + n + n) (blockRot (K + n) n))
    (tensorFragment (s := K + n) (t := K + n) (u := n) (v := n)
      𝔄 𝔊) (strandBundle (K + n + n))
  have E3 := pairCloseCongr
    (Fragment.Equiv.refl (tensorFragment (s := K + n) (t := K + n)
      (u := n) (v := n) 𝔄 𝔊))
    (Fragment.Equiv.relabelEq (strandBundle (K + n + n))
      (outPermEquiv_symm (K + n + n) (blockRot (K + n) n)))
  have E4 := pairCloseCongr
    (Fragment.Equiv.refl (tensorFragment (s := K + n) (t := K + n)
      (u := n) (v := n) 𝔄 𝔊))
    (permFragmentRelabelOutPerm
      (blockRot (K + n) n).symm).symm
  have E5 := pairCloseTensorAbsorb 𝔄 𝔊
    (permFragment (blockRot (K + n) n).symm)
  have E_L : (pairClose
      ((tensorFragment 𝔄 𝔊).compose
        (permFragment (blockRot (K + n) n)))
      (strandBundle (K + n + n))).Equiv
      (pairClose 𝔄
        (partialClose 𝔊
          (permFragment (blockRot (K + n) n).symm))) :=
    E1.trans (E2.trans (E3.trans (E4.trans E5)))
  -- E_R: decompose the RHS closure
  have E_R : (pairClose
      ((𝔄.compose (tensorFragment (strandBundle K) 𝔊)).compose
        (permFragment (blockRot K n)))
      (strandBundle (K + n))).Equiv
      (pairClose 𝔄
        ((permFragment (blockRot K n).symm).compose
          ((tensorFragment (strandBundle K) 𝔊).relabel
            (transposeEquiv (K + n) (K + n))))) :=
    (pairCloseCongr
        (composePermFragment (blockRot K n)
          (𝔄.compose (tensorFragment (strandBundle K) 𝔊)))
        (Fragment.Equiv.refl _)).trans
      ((pairCloseRelabelPerm
          (outPermEquiv (K + n) (blockRot K n)) _ _).trans
        ((pairCloseCongr (Fragment.Equiv.refl _)
            (Fragment.Equiv.relabelEq _
              (outPermEquiv_symm (K + n)
                (blockRot K n)))).trans
          ((pairCloseCongr (Fragment.Equiv.refl _)
              (permFragmentRelabelOutPerm
                (blockRot K n).symm).symm).trans
            (pairCloseComposeRotate 𝔄
              (tensorFragment (strandBundle K) 𝔊)
              (permFragment (blockRot K n).symm)))))
  -- Conclude by iso-invariance and the block splice
  exact f.iso_invariant _ _
    (E_L.trans
      ((pairCloseCongr (Fragment.Equiv.refl 𝔄)
          (partialCloseBlockSplice K n 𝔊)).trans
        E_R.symm))

/-! ### The rotation step at trace values -/

/-- The block rotation step: the trace at `K+n+n` strands
of (blockRot * tensor) equals the trace at `K+n` strands
of (blockRot * pad * accumulated). -/
theorem skeinTrace_block_rot_step (K n : ℕ) (A : skeinEnd f (K + n))
    (g : skeinEnd f n) :
    skeinTrace f (K + n + n)
      (permClass f (K + n + n) (blockRot (K + n) n) *
        blockTensorEnd f A g) =
    skeinTrace f (K + n)
      (permClass f (K + n) (blockRot K n) *
        (blockTensorEnd f (1 : skeinEnd f K) g * A)) := by
  -- Unfold definitions to HomSpace operations
  change HomSpace.traceMap f.val (K + n + n)
    (HomSpace.comp f (K + n + n) (K + n + n) (K + n + n)
      (HomSpace.tensor f (K + n) (K + n) n n A g)
      (HomSpace.ofFragment f.val
        (permFragment (blockRot (K + n) n)))) =
    HomSpace.traceMap f.val (K + n)
      (HomSpace.comp f (K + n) (K + n) (K + n)
        (HomSpace.comp f (K + n) (K + n) (K + n) A
          (HomSpace.tensor f K K n n
            (HomSpace.ofFragment f.val (strandBundle K)) g))
        (HomSpace.ofFragment f.val
          (permFragment (blockRot K n))))
  -- Lift A and g to free-module representatives
  obtain ⟨xa, rfl⟩ := Submodule.Quotient.mk_surjective _ A
  obtain ⟨xg, rfl⟩ := Submodule.Quotient.mk_surjective _ g
  -- Convert to Finsupp level
  change traceFunctional f.val (K + n + n)
      (composeFinsupp (K + n + n) (K + n + n) (K + n + n)
        (tensorFinsupp (K + n) (K + n) n n xa xg)
        (Finsupp.single (permFragment (blockRot (K + n) n)) 1)) =
    traceFunctional f.val (K + n)
      (composeFinsupp (K + n) (K + n) (K + n)
        (composeFinsupp (K + n) (K + n) (K + n) xa
          (tensorFinsupp K K n n
            (Finsupp.single (strandBundle K) 1) xg))
        (Finsupp.single (permFragment (blockRot K n)) 1))
  -- Helper: traceFunctional on a scaled single fragment
  have htr : ∀ (m : ℕ) (H : Fragment (Fin (m + m))) (e : ℂ),
      traceFunctional f.val m (Finsupp.single H e) =
        e * fragTrace f.val H := by
    intro m H e
    rw [show (Finsupp.single H e : Fragment (Fin (m + m)) →₀ ℂ) =
        e • Finsupp.single H 1 by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one],
      map_smul, traceFunctional_single, smul_eq_mul]
  -- Bilinear induction on xa
  induction xa using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero, LinearMap.zero_apply]
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply]
    rw [h₁, h₂]
  | single 𝔄 c =>
    -- Inner induction on xg
    induction xg using Finsupp.induction_linear with
    | zero =>
      simp only [map_zero, LinearMap.zero_apply]
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, LinearMap.add_apply]
      rw [h₁, h₂]
    | single 𝔊 d =>
      -- At fragment classes: reduce to fragTrace_block_rot_step_core
      rw [tensorFinsupp_single, composeFinsupp_single,
        tensorFinsupp_single, composeFinsupp_single,
        composeFinsupp_single, htr, htr,
        fragTrace_block_rot_step_core f K n 𝔄 𝔊]
      ring

/-! ### The block tuple tensor and the block cycle composite -/

/-- The block tuple tensor: tensor product of a tuple of
`n`-strand endomorphisms, as an endomorphism of the `n*k`-strand
object. -/
noncomputable def blockTupleTensor (n : ℕ) :
    ∀ k : ℕ, (Fin k → skeinEnd f n) → skeinEnd f (n * k)
  | 0, _ => 1
  | k + 1, G =>
      blockTensorEnd f
        (blockTupleTensor n k (fun i => G i.castSucc))
        (G (Fin.last k))

/-- The block cycle composite: `G(k-1) * ⋯ * G(0)` in the
`n`-strand endomorphism algebra. -/
noncomputable def blockCycleComp (n : ℕ) :
    ∀ k : ℕ, (Fin k → skeinEnd f n) → skeinEnd f n
  | 0, _ => 1
  | k + 1, G =>
      G (Fin.last k) * blockCycleComp n k (fun i => G i.castSucc)

/-! ### Padding and updating the tuple -/

/-- The padded product updates the last tuple entry. -/
theorem blockPadLeft_mul_blockTupleTensor (K n : ℕ)
    (H : Fin (K + 1) → skeinEnd f n) (g : skeinEnd f n) :
    blockTensorEnd f (1 : skeinEnd f (n * K)) g *
      blockTupleTensor f n (K + 1) H =
    blockTupleTensor f n (K + 1)
      (Function.update H (Fin.last K)
        (g * H (Fin.last K))) := by
  rw [show blockTupleTensor f n (K + 1) H =
      blockTensorEnd f
        (blockTupleTensor f n K (fun i => H i.castSucc))
        (H (Fin.last K)) from rfl]
  rw [show blockTupleTensor f n (K + 1)
      (Function.update H (Fin.last K)
        (g * H (Fin.last K))) =
      blockTensorEnd f
        (blockTupleTensor f n K (fun i =>
          Function.update H (Fin.last K)
            (g * H (Fin.last K)) i.castSucc))
        (Function.update H (Fin.last K)
          (g * H (Fin.last K)) (Fin.last K))
      from rfl]
  rw [Function.update_self]
  have hinit : (fun i : Fin K =>
      Function.update H (Fin.last K)
        (g * H (Fin.last K)) i.castSucc) =
      fun i => H i.castSucc := by
    funext i
    exact Function.update_of_ne
      (Fin.castSucc_lt_last i).ne _ _
  rw [hinit]
  rw [blockTensorEnd_mul, one_mul]

/-- The cycle composite of a last-entry update: the padding
factor peels off. -/
theorem blockCycleComp_update_last (K n : ℕ)
    (H : Fin (K + 1) → skeinEnd f n) (g : skeinEnd f n) :
    blockCycleComp f n (K + 1)
      (Function.update H (Fin.last K) (g * H (Fin.last K))) =
    g * blockCycleComp f n (K + 1) H := by
  rw [show blockCycleComp f n (K + 1)
      (Function.update H (Fin.last K) (g * H (Fin.last K))) =
    Function.update H (Fin.last K) (g * H (Fin.last K))
        (Fin.last K) *
      blockCycleComp f n K (fun i =>
        Function.update H (Fin.last K)
          (g * H (Fin.last K)) i.castSucc) from rfl]
  rw [Function.update_self]
  have hinit : (fun i : Fin K =>
      Function.update H (Fin.last K)
        (g * H (Fin.last K)) i.castSucc) =
      fun i => H i.castSucc := by
    funext i
    exact Function.update_of_ne
      (Fin.castSucc_lt_last i).ne _ _
  rw [hinit]
  rw [show blockCycleComp f n (K + 1) H = H (Fin.last K) *
    blockCycleComp f n K (fun i => H i.castSucc) from rfl]
  rw [mul_assoc]

/-! ### The cycle induction -/

/-- **The block cycle-trace lemma**: the trace of a block
rotation composed with a block tuple tensor is the trace of the
block cycle composite. -/
theorem skeinTrace_block_cycle (n k : ℕ)
    (G : Fin (k + 1) → skeinEnd f n) :
    skeinTrace f (n * (k + 1))
      (permClass f (n * (k + 1))
          (blockPerm n (finRotate (k + 1))) *
        blockTupleTensor f n (k + 1) G) =
    skeinTrace f n (blockCycleComp f n (k + 1) G) := by
  induction k with
  | zero =>
    -- finRotate 1 = 1
    have hrot : finRotate 1 = 1 := Subsingleton.elim _ _
    rw [hrot, blockPerm_one]
    rw [show permClass f (n * 1) (1 : Equiv.Perm (Fin (n * 1))) =
      (1 : skeinEnd f (n * 1)) from map_one (permToEnd f (n * 1))]
    rw [one_mul]
    -- blockTupleTensor f n 1 G = blockTensorEnd f 1 (G 0)
    rw [show blockTupleTensor f n 1 G =
      blockTensorEnd f (1 : skeinEnd f (n * 0)) (G 0) from rfl]
    -- Make additive structure visible for skeinTrace_blockTensorEnd
    change skeinTrace f (0 + n) (blockTensorEnd f (1 : skeinEnd f 0) (G 0)) =
      skeinTrace f n (blockCycleComp f n 1 G)
    -- trace splits: skeinTrace f 0 1 * skeinTrace f n (G 0)
    rw [skeinTrace_blockTensorEnd]
    rw [skeinTrace_zero_one, one_mul]
    -- blockCycleComp f n 1 G = G 0 * 1 = G 0
    rw [show blockCycleComp f n 1 G =
      G (Fin.last 0) * (1 : skeinEnd f n) from rfl]
    rw [show (Fin.last 0 : Fin 1) = (0 : Fin 1) from rfl]
    rw [mul_one]
  | succ m ih =>
    -- Unfold blockTupleTensor at m+2
    rw [show blockTupleTensor f n (m + 2) G =
      blockTensorEnd f
        (blockTupleTensor f n (m + 1)
          (fun i => G i.castSucc))
        (G (Fin.last (m + 1))) from rfl]
    -- Bridge: blockPerm n (finRotate (m+2)) = blockRot (n*(m+1)) n
    rw [blockPerm_finRotate_eq_blockRot]
    -- Make additive structure visible for the rot step
    change skeinTrace f (n * m + n + n)
        (permClass f (n * m + n + n) (blockRot (n * m + n) n) *
          blockTensorEnd f
            (blockTupleTensor f n (m + 1) (fun i => G i.castSucc))
            (G (Fin.last (m + 1)))) =
      skeinTrace f n (blockCycleComp f n (m + 2) G)
    -- Apply the block rotation step (K = n*m)
    rw [skeinTrace_block_rot_step]
    -- Fold the padding into the tuple
    rw [blockPadLeft_mul_blockTupleTensor]
    -- Bridge back: blockRot (n*m) n = blockPerm n (finRotate (m+1))
    rw [← blockPerm_finRotate_eq_blockRot]
    -- Reshape arity for IH: n * m + n ≡ n * (m + 1)
    change skeinTrace f (n * (m + 1))
        (permClass f (n * (m + 1)) (blockPerm n (finRotate (m + 1))) *
          blockTupleTensor f n (m + 1)
            (Function.update (fun i => G i.castSucc) (Fin.last m)
              (G (Fin.last (m + 1)) * G (Fin.last m).castSucc))) =
      skeinTrace f n (blockCycleComp f n (m + 2) G)
    -- Apply IH
    rw [ih]
    -- Fold the cycle composite
    rw [blockCycleComp_update_last]
    -- Match the cycle composite definition
    rw [show blockCycleComp f n (m + 2) G =
      G (Fin.last (m + 1)) *
        blockCycleComp f n (m + 1) (fun i => G i.castSucc)
      from rfl]

/-! ### Constant tuples -/

/-- The block cycle composite of a constant tuple is the power. -/
theorem blockCycleComp_const (n k : ℕ) (g : skeinEnd f n) :
    blockCycleComp f n k (fun _ => g) = g ^ k := by
  induction k with
  | zero =>
    rw [pow_zero]
    rfl
  | succ k ih =>
    rw [show blockCycleComp f n (k + 1) (fun _ => g) =
      g * blockCycleComp f n k (fun _ => g) from rfl,
      ih, ← pow_succ']

/-- The block tuple tensor of a constant tuple is the block
power. -/
theorem blockTupleTensor_const (n k : ℕ) (g : skeinEnd f n) :
    blockTupleTensor f n k (fun _ => g) = blockPow f n g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show blockTupleTensor f n (k + 1) (fun _ => g) =
      blockTensorEnd f
        (blockTupleTensor f n k (fun _ => g)) g from rfl,
      ih]
    rfl

/-! ### The block cycle trace -/

/-- **The block cycle trace**: closing the block rotation against
`c+1` diagonal blocks yields the trace of the `(c+1)`-th power. -/
theorem skeinTrace_blockCycle' (n : ℕ) (g : skeinEnd f n) (c : ℕ) :
    skeinTrace f (n * (c + 1))
      (permClass f (n * (c + 1)) (blockPerm n (finRotate (c + 1))) *
        blockPow f n g (c + 1)) =
    skeinTrace f n (g ^ (c + 1)) := by
  rw [← blockTupleTensor_const,
    skeinTrace_block_cycle,
    blockCycleComp_const]

end RS
