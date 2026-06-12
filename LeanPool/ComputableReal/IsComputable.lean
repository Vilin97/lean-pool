/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import LeanPool.ComputableReal.ComputableReal
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Peel

/-!
# The `IsComputable` typeclass

`IsComputable x` packages a `ComputableℝSeq` converging to the real number `x`: an explicit
sequence of rational interval approximations. Closure instances (for arithmetic, powers, scalar
multiples) and `Decidable` instances for comparisons are provided, along with a tool for lifting
continuous functions defined by locally-uniformly converging rational approximations.

Since a `ComputableℝSeq` is an arbitrary function `ℕ → ℚInterval` (with convergence proofs)
rather than recursive data, this is not computability in the computable-analysis sense, and the
comparison instances below are classical (`noncomputable`, via sign information on the limit).
-/

/-- Type class stating that `x : ℝ` carries a `ComputableℝSeq`: an explicit sequence of rational
interval approximations converging to `x`. Like `Decidable`, it carries data with it, and
classically every real number admits such a sequence; its value lies in the explicit
approximations it provides, not in a computability guarantee. -/
class IsComputable (x : ℝ) : Type where
    /-- A computable sequence representing `x`. -/
    seq : ComputableℝSeq
    /-- The sequence converges to `x`. -/
    prop : seq.val = x

namespace IsComputable

/-- Turns one `IsComputable` into another one, given a proof that they're equal. This is directly
analogous to `decidable_of_iff`, as a way to avoid `Eq.rec` on data-carrying instances. -/
@[reducible] def liftEq {x y : ℝ} (h : x = y) :
    IsComputable x → IsComputable y :=
  fun ⟨sx, hsx⟩ ↦ ⟨sx, h ▸ hsx⟩

/-- Definition of `lift`. -/
@[reducible] def lift (fr : ℝ → ℝ) (fs : ComputableℝSeq → ComputableℝSeq)
    (h : ∀ a, (fs a).val = fr a.val) :
    IsComputable x → IsComputable (fr x) :=
  fun ⟨sx, hsx⟩ ↦ ⟨fs sx, hsx ▸ h sx⟩

/-- Definition of `lift₂`. -/
@[reducible] def lift₂ (fr : ℝ → ℝ → ℝ) (fs : ComputableℝSeq → ComputableℝSeq → ComputableℝSeq)
    (h : ∀ a b, (fs a b).val = fr a.val b.val) :
    IsComputable x → IsComputable y → IsComputable (fr x y) :=
  fun ⟨sx, hsx⟩ ⟨sy, hsy⟩ ↦ ⟨fs sx sy, hsx ▸ hsy ▸ h sx sy⟩

instance instComputableNat (n : ℕ) : IsComputable n :=
  ⟨ComputableℝSeq.ofRat n, ComputableℝSeq.val_natCast⟩

instance instComputableInt (z : ℤ) : IsComputable z :=
  ⟨ComputableℝSeq.ofRat z, ComputableℝSeq.val_intCast⟩

instance instComputableRat (q : ℚ) : IsComputable q :=
  ⟨ComputableℝSeq.ofRat q, ComputableℝSeq.val_ratCast⟩

instance instComputableOfNat1 : IsComputable
    (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real inferInstance)) :=
  ⟨1, ComputableℝSeq.val_one⟩

instance instComputableOfNat0 : IsComputable
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real inferInstance)) :=
  ⟨0, ComputableℝSeq.val_zero⟩

instance instComputableOfNatAtLeastTwo : (n : ℕ) → [n.AtLeastTwo] → IsComputable ofNat(n) :=
  fun _ _ ↦ ⟨
    ⟨fun _ ↦ ⟨⟨_, _⟩, rfl.le⟩,
      IsCauSeq.const _, IsCauSeq.const _,
      fun _ ↦ by simpa using ⟨rfl.le, rfl.le⟩,
      by rfl⟩,
    ComputableℝSeq.val_eq_mk_lb _⟩

instance instComputableNeg (x : ℝ) [hx : IsComputable x] : IsComputable (-x) :=
  lift _ (- ·) ComputableℝSeq.val_neg hx

noncomputable instance instComputableInv (x : ℝ) [hx : IsComputable x] : IsComputable (x⁻¹) :=
  lift _ (·⁻¹) ComputableℝSeq.val_inv hx

instance instComputableAdd [hx : IsComputable x] [hy : IsComputable y] : IsComputable (x + y) :=
  lift₂ _ (· + ·) ComputableℝSeq.val_add hx hy

instance instComputableSub [hx : IsComputable x] [hy : IsComputable y] : IsComputable (x - y) :=
  lift₂ _ (· - ·) ComputableℝSeq.val_sub hx hy

instance instComputableMul [hx : IsComputable x] [hy : IsComputable y] : IsComputable (x * y) :=
  lift₂ _ (· * ·) ComputableℝSeq.val_mul hx hy

noncomputable instance instComputableDiv [hx : IsComputable x] [hy : IsComputable y] : IsComputable
  (x / y) :=
  lift₂ _ (· / ·) ComputableℝSeq.val_div hx hy

instance instComputableNatPow [hx : IsComputable x] (n : ℕ) : IsComputable (x ^ n) := by
  /-TODO(mul_assoc)
  Redo this to use native powering on the ComputableℝSeq. This avoids more costly
  (and inaccurate) interval multiplications. That will also turn it into exponentiation
  by squaring.
  -/
  induction n
  · rw [pow_zero]
    infer_instance
  · rw [pow_succ]
    infer_instance

noncomputable instance instComputableZPow [hx : IsComputable x] (z : ℤ) : IsComputable (x ^ z) := by
  cases z
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    infer_instance
  · simp only [zpow_negSucc]
    infer_instance

noncomputable instance instComputableNSMul [hx : IsComputable x] (n : ℕ) : IsComputable (n • x) :=
  lift _ (n • ·) (by
    --TODO move to a ComputableℝSeq lemma
    intro a
    induction n
    · simp
    · rename_i ih
      simp [ih, succ_nsmul, add_mul]
    ) hx

noncomputable instance instComputableZSMul [hx : IsComputable x] (z : ℤ) : IsComputable (z • x) :=
  by
  rw [zsmul_eq_mul]
  infer_instance

noncomputable instance instComputableQSMul [hx : IsComputable x] (q : ℚ) : IsComputable (q • x) :=
  by
  change IsComputable (_ * _)
  infer_instance

/-- When expressions happen to be `IsComputable`, we can get a decidability instance by
lifting them to a comparison on the `ComputableℝSeq`s. The comparison there is classical
(it goes through the noncomputable `ComputableℝSeq.sign`), so this instance is
`noncomputable` and carries no algorithmic content. -/
noncomputable instance instDecidableLE [hx : IsComputable x] [hy : IsComputable y] : Decidable (x ≤
  y) :=
  decidable_of_decidable_of_iff (p := Computableℝ.mk hx.seq ≤ Computableℝ.mk hy.seq) (by
    simp only [← Computableℝ.le_iff_le, Computableℝ.val_mk_eq_val, hx.prop, hy.prop]
  )

noncomputable instance instDecidableEq [hx : IsComputable x] [hy : IsComputable y] : Decidable (x =
  y) :=
  decidable_of_decidable_of_iff (p := (Computableℝ.mk hx.seq = Computableℝ.mk hy.seq)) (by
    simp only [← Computableℝ.eq_iff_eq_val, Computableℝ.val_mk_eq_val, hx.prop, hy.prop]
  )

noncomputable instance instDecidableLT [hx : IsComputable x] [hy : IsComputable y] : Decidable (x <
  y) :=
  decidable_of_decidable_of_iff (p := Computableℝ.mk hx.seq < Computableℝ.mk hy.seq) (by
    simp only [← Computableℝ.lt_iff_lt, Computableℝ.val_mk_eq_val, hx.prop, hy.prop]
  )

noncomputable instance instDecidableLEval (x y : ComputableℝSeq) : Decidable (x.val ≤ y.val) :=
  @instDecidableLE x.val y.val ⟨x, rfl⟩ ⟨y,rfl⟩

noncomputable instance instDecidableLTval (x y : ComputableℝSeq) : Decidable (x.val < y.val) :=
  @instDecidableLT x.val y.val ⟨x, rfl⟩ ⟨y,rfl⟩

end IsComputable


/-- This is very similar to the statement
`TendstoLocallyUniformly (fun n x ↦ (F n x : ℝ)) (fun (q : ℚ) ↦ f q) .atTop`
but that only uses neighborhoods within the rationals, which is a strictly
weaker condition. This uses neighborhoods in the ambient space, the reals.
-/
def TendstoLocallyUniformlyWithout (F : ℕ → ℚ → ℚ) (f : ℝ → ℝ) : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∀ (x : ℝ), ∃ t ∈ nhds x, ∃ a, ∀ (b : ℕ), a ≤ b → ∀ (y : ℚ), ↑y ∈ t →
    |f y - ↑(F b y)| < ε

theorem Real_mk_of_TendstoLocallyUniformly' (fImpl : ℕ → ℚ → ℚ) (f : ℝ → ℝ)
    (hfImpl : TendstoLocallyUniformlyWithout (fImpl) (f))
    (hf : Continuous f)
    (x : CauSeq ℚ abs)
    : ∃ (h : IsCauSeq abs (fun n ↦ fImpl n (x n))), Real.mk ⟨_, h⟩ = f (.mk x) := by
  apply Real.of_near
  simp only [Metric.continuous_iff, gt_iff_lt, Real.dist_eq] at hf
  rcases x with ⟨x, hx⟩
  intro ε hε
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hf (.mk ⟨x, hx⟩) _ (half_pos hε)
  obtain ⟨i₁, hi₁⟩ := cauchy_real_mk ⟨x, hx⟩ δ₁ hδ₁pos
  obtain ⟨i₂_nhd, hi₂_nhds, i₃, hi₃⟩ := hfImpl _ (half_pos hε) (.mk ⟨x, hx⟩)
  obtain ⟨nl, nu, ⟨hnl, hnu⟩, hnd_sub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hi₂_nhds
  replace hnd_sub : ∀ (r : ℚ), nl < r ∧ r < nu → ↑r ∈ i₂_nhd := fun r a => hnd_sub a
  replace hi₃ : ∀ (b : ℕ), i₃ ≤ b → ∀ (y : ℚ), nl < y ∧ y < nu → |f ↑y - ↑(fImpl b y)| < (ε / 2) :=
    by
    peel hi₃
    exact fun h ↦ this (hnd_sub _ h)
  set ε_nhd := min (nu - (.mk ⟨x,hx⟩)) ((.mk ⟨x,hx⟩) - nl) with hε_nhd
  obtain ⟨i₄, hi₄⟩ := cauchy_real_mk ⟨x,hx⟩ (ε_nhd / 2) (by
    rw [hε_nhd, gt_iff_lt, ← min_div_div_right (zero_le_two), lt_inf_iff]
    constructor <;> linarith)
  have hεn₁ : ε_nhd ≤ _ := inf_le_left
  have hεn₂ : ε_nhd ≤ _ := inf_le_right
  set i := max i₁ (max i₃ i₄) with hi
  use i
  intro j hj
  simp only [hi, ge_iff_le, sup_le_iff] at hj
  specialize hδ₁ _ (hi₁ j (by linarith))
  specialize hi₄ j (by linarith)
  specialize hi₃ j (by linarith) (x j) (by
    constructor
    · linarith [sub_le_of_abs_sub_le_left hi₄.le]
    · linarith [sub_le_of_abs_sub_le_right hi₄.le]
  )
  calc |↑(fImpl j (x j)) - f (Real.mk ⟨x, hx⟩)| =
    |(↑(fImpl j (x j)) - f ↑(x j)) + (f ↑(x j) - f (Real.mk ⟨x, hx⟩))| := by congr; ring_nf
    _ ≤ |(↑(fImpl j (x j)) - f ↑(x j))| + |(f ↑(x j) - f (Real.mk ⟨x, hx⟩))| := abs_add_le _ _
    _ < ε := by rw [abs_sub_comm]; linarith

open scoped QInterval

namespace ComputableℝSeq

/-- Definition of `ofTendstoLocallyUniformlyContinuous`. -/
def ofTendstoLocallyUniformlyContinuous
    {f : ℝ → ℝ} (hf : Continuous f)
    (fImpl : ℕ → ℚInterval → ℚInterval)
    (fImpl_l : ℕ → ℚ → ℚ)
    (fImpl_u : ℕ → ℚ → ℚ)
    (hlb : ∀ (n : ℕ) (q : ℚInterval) (x : ℝ), x ∈ q → fImpl_l n q.fst ≤ f x)
    (hub : ∀ (n : ℕ) (q : ℚInterval) (x : ℝ), x ∈ q → f x ≤ fImpl_u n q.snd)
    (hImplDef : ∀ n q, fImpl n q = ⟨⟨fImpl_l n q.fst, fImpl_u n q.snd⟩,
      Rat.cast_le.mp ((hlb n q q.fst ⟨le_refl _, Rat.cast_le.mpr q.2⟩).trans
      (hub n q q.fst ⟨le_refl _, Rat.cast_le.mpr q.2⟩))⟩)
    (hTLU_l : TendstoLocallyUniformlyWithout fImpl_l f)
    (hTLU_u : TendstoLocallyUniformlyWithout fImpl_u f)
    (x : ComputableℝSeq) : ComputableℝSeq :=
  mk
  (x := f x.val)
  (lub := fun n ↦ fImpl n (x.lub n))
  (hcl := by
    obtain ⟨w, _⟩ := Real_mk_of_TendstoLocallyUniformly' fImpl_l f hTLU_l hf x.lb
    simp_rw [hImplDef]
    exact w
  )
  (hcu := by
    obtain ⟨w, _⟩ := Real_mk_of_TendstoLocallyUniformly' fImpl_u f hTLU_u hf x.ub
    simp_rw [hImplDef]
    exact w
  )
  (hlb := fun n ↦ by simp_rw [hImplDef]; exact hlb n (x.lub n) x.val ⟨x.hlb n, x.hub n⟩)
  (hub := fun n ↦ by simp_rw [hImplDef]; exact hub n (x.lub n) x.val ⟨x.hlb n, x.hub n⟩)
  (heq := by
    obtain ⟨_, h₁⟩ := Real_mk_of_TendstoLocallyUniformly' fImpl_l f hTLU_l hf x.lb
    obtain ⟨_, h₂⟩ := Real_mk_of_TendstoLocallyUniformly' fImpl_u f hTLU_u hf x.ub
    simp only [hImplDef, ← Real.mk_eq]
    rw [lb_eq_ub] at h₁
    exact h₁.trans h₂.symm
  )

@[simp]
theorem val_ofTendstoLocallyUniformlyContinuous (f) (hf : Continuous f) (fI fl fu h₁ h₂ h₃ h₄ h₅
  a)
  : (ofTendstoLocallyUniformlyContinuous hf fI fl fu h₁ h₂ h₃ h₄ h₅ a).val =
    f a.val :=
  ComputableℝSeq.mk_val_eq_val

end ComputableℝSeq

--mostly a helper for numerical investigation
/-- Definition of `toDecimal`. -/
def Rat.toDecimal (q : ℚ) (prec : ℕ := 20) :=
  let p : ℚ → String := fun q ↦
    (q.floor.repr).append <| ".".append <| (10^prec * (q - q.floor)).floor.repr.leftpad prec '0'
  if q < 0 then "-".append (p (-q)) else if q = 0 then "0" else p q
