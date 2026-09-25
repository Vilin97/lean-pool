/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.Length

/-!
# Length lower bounds from orthogonal idempotents

A family of pairwise-orthogonal nonzero idempotent endomorphisms
of an object `Y` of an abelian category splits `Y` into as many
nonzero pieces, so it bounds the composition length of `Y` from
below.  In the bound-shaped formulation of `LengthLE`
(`RS/Definitions.lean`) this reads: `k` such endomorphisms
together with `LengthLE Y N` force `k ≤ N + 1`.

The proof forms the partial sums `E n = f 0 + ⋯ + f n`, which are
again idempotent by orthogonality, realises each as the subobject
`ker (𝟙 Y - E n)`, and shows the resulting chain is strictly
increasing: a collapse of consecutive kernels would factor
`f (n + 1)` through `ker (𝟙 Y - E n)`, where it is annihilated by
orthogonality, contradicting `f (n + 1) ≠ 0`.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Limits

universe v u

section Helpers

variable {C : Type u}

/-- An endomorphism, retyped as a morphism, so that morphism-level
notation (`≫`, subtraction of parallel morphisms) elaborates
without fuss. -/
private def endHom [Category.{v} C]
    {Y : C} (e : End Y) : Y ⟶ Y := e

/-- A finite family of endomorphisms, extended by zero to a family
indexed by `ℕ`. -/
private def extendZero [Category.{v} C] [Abelian C]
    {Y : C} {k : ℕ} (f : Fin k → End Y) (n : ℕ) :
    End Y :=
  if h : n < k then f ⟨n, h⟩ else 0

/-- Below `k`, the extension agrees with the original family. -/
private lemma extendZero_of_lt [Category.{v} C] [Abelian C]
    {Y : C} {k : ℕ} (f : Fin k → End Y)
    {n : ℕ} (h : n < k) : extendZero f n = f ⟨n, h⟩ :=
  dite_eq_left h

/-- The extension by zero inherits idempotence. -/
private lemma extendZero_idem [Category.{v} C] [Abelian C]
    {Y : C} {k : ℕ} {f : Fin k → End Y}
    (hidem : ∀ i, f i * f i = f i) (n : ℕ) :
    extendZero f n * extendZero f n = extendZero f n := by
  unfold extendZero
  split
  · exact hidem _
  · exact zero_mul 0

/-- The extension by zero inherits pairwise orthogonality. -/
private lemma extendZero_orth [Category.{v} C] [Abelian C]
    {Y : C} {k : ℕ} {f : Fin k → End Y}
    (horth : ∀ i j, i ≠ j → f i * f j = 0) {m n : ℕ} (h : m ≠ n) :
    extendZero f m * extendZero f n = 0 := by
  unfold extendZero
  split
  · split
    · exact horth _ _ fun he => h (congrArg Fin.val he)
    · exact mul_zero _
  · exact zero_mul _

/-- The partial sum `g 0 + ⋯ + g n` of a family of
endomorphisms. -/
private def partialSum [Category.{v} C] [Abelian C]
    {Y : C} (g : ℕ → End Y) (n : ℕ) : End Y :=
  ∑ i ∈ Finset.range (n + 1), g i

/-- Multiplying a partial sum of an orthogonal idempotent family
by a member already collected picks out that member. -/
private lemma partialSum_mul [Category.{v} C] [Abelian C]
    {Y : C} {g : ℕ → End Y}
    (hidem : ∀ i, g i * g i = g i)
    (horth : ∀ i j, i ≠ j → g i * g j = 0)
    {j n : ℕ} (h : j ≤ n) : partialSum g n * g j = g j := by
  unfold partialSum
  rw [Finset.sum_mul, Finset.sum_eq_single j
    (fun b _ hb => horth b j hb)
    (fun hj => absurd (Finset.mem_range.mpr (by omega)) hj)]
  exact hidem j

/-- A partial sum of an orthogonal family annihilates the members
not yet collected. -/
private lemma partialSum_mul_of_lt [Category.{v} C] [Abelian C]
    {Y : C} {g : ℕ → End Y}
    (horth : ∀ i j, i ≠ j → g i * g j = 0)
    {j n : ℕ} (h : n < j) : partialSum g n * g j = 0 := by
  unfold partialSum
  rw [Finset.sum_mul]
  exact Finset.sum_eq_zero fun i hi =>
    horth i j (by have := Finset.mem_range.mp hi; omega)

/-- Consecutive partial sums of an orthogonal idempotent family
multiply to the shorter one. -/
private lemma partialSum_succ_mul [Category.{v} C] [Abelian C]
    {Y : C} {g : ℕ → End Y}
    (hidem : ∀ i, g i * g i = g i)
    (horth : ∀ i j, i ≠ j → g i * g j = 0) (n : ℕ) :
    partialSum g (n + 1) * partialSum g n = partialSum g n := by
  have h1 : partialSum g n = ∑ i ∈ Finset.range (n + 1), g i := rfl
  rw [h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi =>
    partialSum_mul hidem horth
      (by have := Finset.mem_range.mp hi; omega)

/-- The subobject of `Y` carried by an idempotent `e`, realised as
the kernel of `𝟙 Y - e`. -/
private noncomputable def idemKer [Category.{v} C] [Abelian C]
    {Y : C} (e : End Y) :
    Subobject Y :=
  Subobject.mk (kernel.ι (𝟙 Y - endHom e))

/-- The kernel inclusion of `𝟙 Y - e` is fixed by `e`. -/
private lemma kernel_comp_self [Category.{v} C] [Abelian C]
    {Y : C} (e : End Y) :
    kernel.ι (𝟙 Y - endHom e) ≫ endHom e =
      kernel.ι (𝟙 Y - endHom e) := by
  have h := kernel.condition (𝟙 Y - endHom e)
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at h
  exact h.symm

/-- Anything that factors through the kernel of `𝟙 Y - e` is fixed
by `e`. -/
private lemma comp_self_of_factors [Category.{v} C] [Abelian C]
    {Y T : C} {e : End Y}
    {x : T ⟶ Y} {w : T ⟶ kernel (𝟙 Y - endHom e)}
    (hw : w ≫ kernel.ι (𝟙 Y - endHom e) = x) : x ≫ endHom e = x := by
  rw [← hw, Category.assoc, kernel_comp_self]

/-- If `e' * e = e` then the subobject carried by `e` is contained
in the one carried by `e'`. -/
private lemma idemKer_le [Category.{v} C] [Abelian C]
    {Y : C} {e e' : End Y} (h : e' * e = e) :
    idemKer e ≤ idemKer e' := by
  have hc : endHom e ≫ endHom e' = endHom e := by
    rw [← End.mul_def]; exact h
  have hk : kernel.ι (𝟙 Y - endHom e) ≫ (𝟙 Y - endHom e') = 0 := by
    have h2 : kernel.ι (𝟙 Y - endHom e) ≫ endHom e' =
        kernel.ι (𝟙 Y - endHom e) := by
      calc kernel.ι (𝟙 Y - endHom e) ≫ endHom e'
          = (kernel.ι (𝟙 Y - endHom e) ≫ endHom e) ≫ endHom e' := by
            rw [kernel_comp_self]
        _ = kernel.ι (𝟙 Y - endHom e) ≫ (endHom e ≫ endHom e') :=
            Category.assoc _ _ _
        _ = kernel.ι (𝟙 Y - endHom e) := by
            rw [hc, kernel_comp_self]
    rw [Preadditive.comp_sub, Category.comp_id, h2, sub_self]
  exact Subobject.mk_le_mk_of_comm
    (kernel.lift _ (kernel.ι _) hk) (kernel.lift_ι _ _ _)

/-- If the subobjects carried by two idempotents coincide, an
endomorphism fixed by the second and annihilated by the first must
vanish. -/
private lemma eq_zero_of_idemKer_eq [Category.{v} C] [Abelian C]
    {Y : C} {e e' a : End Y}
    (hfix : e' * a = a) (hkill : e * a = 0)
    (hU : idemKer e = idemKer e') : a = 0 := by
  have hfix' : endHom a ≫ endHom e' = endHom a := by
    rw [← End.mul_def]; exact hfix
  have hkill' : endHom a ≫ endHom e = 0 := by
    rw [← End.mul_def]; exact hkill
  have hz : endHom a ≫ (𝟙 Y - endHom e') = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id, hfix', sub_self]
  have hle : idemKer e' ≤ idemKer e := hU.ge
  unfold idemKer at hle
  have ha : (kernel.lift (𝟙 Y - endHom e') (endHom a) hz ≫
      Subobject.ofMkLEMk _ _ hle) ≫ kernel.ι (𝟙 Y - endHom e) =
      endHom a := by
    rw [Category.assoc, Subobject.ofMkLEMk_comp, kernel.lift_ι]
  have hae : endHom a ≫ endHom e = endHom a := comp_self_of_factors ha
  rw [hkill'] at hae
  exact hae.symm

end Helpers

/-- **Orthogonal idempotents bound length from below.**  In an
abelian category, a family of `k` pairwise-orthogonal nonzero
idempotent endomorphisms of `Y` forces the composition length of
`Y` to be at least `k`; with the bound `LengthLE Y N` this reads
`k ≤ N + 1`. -/
theorem le_of_orthogonal_idempotents {C : Type u} [Category.{v} C]
    [Abelian C] {Y : C} {N k : ℕ} (hlen : LengthLE Y N)
    (f : Fin k → End Y)
    (hidem : ∀ i, f i * f i = f i)
    (horth : ∀ i j, i ≠ j → f i * f j = 0)
    (hne : ∀ i, f i ≠ 0) :
    k ≤ N + 1 := by
  by_contra hk
  have hgidem := extendZero_idem hidem
  have hgorth : ∀ m n, m ≠ n →
      extendZero f m * extendZero f n = 0 :=
    fun m n h => extendZero_orth horth h
  have hstep : ∀ n, idemKer (partialSum (extendZero f) n) ≤
      idemKer (partialSum (extendZero f) (n + 1)) :=
    fun n => idemKer_le (partialSum_succ_mul hgidem hgorth n)
  have hmono :
      Monotone fun n => idemKer (partialSum (extendZero f) n) :=
    monotone_nat_of_le_succ hstep
  have hstrict : ∀ n, n + 1 < k →
      idemKer (partialSum (extendZero f) n) ≠
        idemKer (partialSum (extendZero f) (n + 1)) := by
    intro n hn hEq
    have hz : extendZero f (n + 1) = 0 :=
      eq_zero_of_idemKer_eq
        (partialSum_mul hgidem hgorth (le_refl (n + 1)))
        (partialSum_mul_of_lt hgorth (Nat.lt_succ_self n)) hEq
    exact hne ⟨n + 1, hn⟩ ((extendZero_of_lt f hn).symm.trans hz)
  refine hlen
    (fun i : Fin (N + 2) =>
      idemKer (partialSum (extendZero f) i)) ?_
  intro a b hab
  have hab' : (a : ℕ) < (b : ℕ) := hab
  have hb := b.isLt
  refine lt_of_lt_of_le
    (lt_of_le_of_ne (hstep a) (hstrict a (by omega))) (hmono ?_)
  omega

end RS
