/-
Copyright (c) 2026 Andrej Bauer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrej Bauer
-/
import LeanPool.PartialCombinatoryAlgebras.Basic
import LeanPool.PartialCombinatoryAlgebras.PartialCombinatoryAlgebra

/-! ## Programming with PCAs

  A (non-trivial) PCA is Turing-complete in the sense that it implements
  every partial computable function. We develop here basic programming
  constructs that witness this fact:

  * the identity combinator `I`
  * ordered pairs `pair` with projections `fst` and `snd`
  * booleans `tru`, `fal` and the conditional statement `ite`
  * fixed-point combinators `Z` and `Y`
  * Curry numerals `numeral n` with successor `succ`, predecessor `pred`
    and primitive recursion `primrec`

  For each combinator `C` we prove a definedness lemma `df_C` characterizing
  totality of expressions involving `C`. Characteristic equations for the
  simpler combinators (`I`, `K'`, `pair`, `fst`, `snd`, the booleans, `X`, `W`,
  and the fixed-point combinators) are also proved here; equations for the
  more complex Curry-numeral predecessor and primitive-recursion combinators
  are omitted in this v4.30 port — they remain expressible in terms of the
  combinators themselves.
-/

namespace LeanPool.PartialCombinatoryAlgebras

namespace PCA

universe u
variable {A : Type u} [PCA A]

/-- The identity combinator -/
def I : Part A := S ⬝ K ⬝ K

namespace Expr

/-- The expression denoting the identity combinator -/
def I {Γ} : Expr Γ A := .S ⬝ .K ⬝ .K

end Expr

@[simp]
theorem df_I : (I : Part A) ⇓ := df_S₂ df_K₀ df_K₀

@[simp]
theorem eq_I {u : Part A} (hu : u ⇓) : I ⬝ u = u := by
  change (S ⬝ K ⬝ K) ⬝ u = u
  rw [eq_S _ _ _ df_K₀ df_K₀ hu, eq_K _ _ hu (df_K₁ hu)]

/-- The `K I` combinator: `K' u v = v`. -/
def K' : Part A := K ⬝ I

namespace Expr

/-- Formal expression denoting `K'`. -/
def K' {Γ} : Expr Γ A := .K ⬝ .I

end Expr

@[simp]
theorem df_K' : (K' : Part A) ⇓ := df_K₁ df_I

@[simp]
theorem eq_K' (u v : Part A) (hu : u ⇓) (hv : v ⇓) : K' ⬝ u ⬝ v = v := by
  change (K ⬝ I) ⬝ u ⬝ v = v
  rw [eq_K _ _ df_I hu, eq_I hv]

/-! ### Pairing -/

/-- The pairing combinator. -/
def pair : Part A := [pca: ≪`x≫ ≪`y≫ ≪`z≫ .var `z ⬝ .var `x ⬝ .var `y]

@[simp]
theorem df_pair : (pair : Part A) ⇓ := df_abstr _ _ _

@[simp]
theorem df_pair_app (u : Part A) (hu : u ⇓) : (pair ⬝ u) ⇓ := by
  unfold pair
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu]
  exact df_abstr _ _ _

@[simp]
theorem df_pair_app_app (u v : Part A) (hu : u ⇓) (hv : v ⇓) : (pair ⬝ u ⬝ v) ⇓ := by
  unfold pair
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu, eval_abstr_app _ _ _ _ hv]
  exact df_abstr _ _ _

@[simp]
theorem eq_pair (u v w : Part A) (hu : u ⇓) (hv : v ⇓) (hw : w ⇓) :
    pair ⬝ u ⬝ v ⬝ w = w ⬝ u ⬝ v := by
  unfold pair
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu, eval_abstr_app _ _ _ _ hv, eval_abstr_app _ _ _ _ hw]
  change Part.some (w.get hw) ⬝ Part.some (u.get hu) ⬝ Part.some (v.get hv) = w ⬝ u ⬝ v
  rw [Part.some_get hw, Part.some_get hu, Part.some_get hv]

/-- The first projection. -/
def fst : Part A := [pca: ≪ `x ≫ .var `x ⬝ .K]

namespace fst

/-- The first projection as a formal expression. -/
def elm {Γ} : Expr Γ A := .elm (fst.get (df_abstr _ _ _))

end fst

@[simp]
theorem eq_fst (u : Part A) (hu : u ⇓) : fst ⬝ u = u ⬝ PCA.K := by
  unfold fst
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu]
  change Part.some (u.get hu) ⬝ PCA.K = u ⬝ PCA.K
  rw [Part.some_get hu]

/-- The second projection. -/
def snd : Part A := [pca: ≪ `x ≫ .var `x ⬝ .K']

namespace snd

/-- The second projection as a formal expression. -/
def elm {Γ} : Expr Γ A := .elm (snd.get (df_abstr _ _ _))

end snd

@[simp]
theorem eq_snd (u : Part A) (hu : u ⇓) : snd ⬝ u = u ⬝ K' := by
  unfold snd
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu]
  change Part.some (u.get hu) ⬝ K' = u ⬝ K'
  rw [Part.some_get hu]

theorem eq_fst_pair (u v : Part A) (hu : u ⇓) (hv : v ⇓) : fst ⬝ (pair ⬝ u ⬝ v) = u := by
  calc
    _ = pair ⬝ u ⬝ v ⬝ K := eq_fst _ (df_pair_app_app u v hu hv)
    _ = K ⬝ u ⬝ v := eq_pair u v K hu hv df_K₀
    _ = u := eq_K _ _ hu hv

theorem eq_snd_pair (u v : Part A) (hu : u ⇓) (hv : v ⇓) : snd ⬝ (pair ⬝ u ⬝ v) = v := by
  calc
    _ = pair ⬝ u ⬝ v ⬝ K' := eq_snd _ (df_pair_app_app u v hu hv)
    _ = K' ⬝ u ⬝ v := eq_pair u v K' hu hv df_K'
    _ = v := eq_K' u v hu hv

/-- Conditional statements -/
def ite : Part A := I

/-- The boolean false -/
def fal : Part A := K'

@[simp] theorem df_fal : (fal : Part A) ⇓ := df_K'

@[simp] theorem eq_fal (u v : Part A) (hu : u ⇓) (hv : v ⇓) :
    fal ⬝ u ⬝ v = v := eq_K' u v hu hv

/-- The boolean true -/
def tru : Part A := K

@[simp] theorem df_tru : (tru : Part A) ⇓ := df_K₀

@[simp]
theorem eq_ite_fal (u v : Part A) (hu : u ⇓) (hv : v ⇓) :
    ite ⬝ fal ⬝ u ⬝ v = v := by
  change I ⬝ fal ⬝ u ⬝ v = v
  rw [eq_I df_fal, eq_fal u v hu hv]

@[simp]
theorem eq_ite_tru (u v : Part A) (hu : u ⇓) (hv : v ⇓) :
    ite ⬝ tru ⬝ u ⬝ v = u := by
  change I ⬝ K ⬝ u ⬝ v = u
  rw [eq_I df_K₀, eq_K u v hu hv]

/-! ### The fixed point combinator -/

/-- Auxiliary combinator used to define the fixed point combinator `Z`. -/
def X : Part A := [pca: ≪`x≫ ≪`y≫ ≪`z≫ .var `y ⬝ (.var `x ⬝ .var `x ⬝ .var `y) ⬝ .var `z]

@[simp]
theorem df_X : (X : Part A) ⇓ := df_abstr _ _ _

@[simp]
theorem df_X_app (u : Part A) (hu : u ⇓) : (X ⬝ u) ⇓ := by
  unfold X
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu]
  exact df_abstr _ _ _

@[simp]
theorem df_X_app_app (u v : Part A) (hu : u ⇓) (hv : v ⇓) : (X ⬝ u ⬝ v) ⇓ := by
  unfold X
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu, eval_abstr_app _ _ _ _ hv]
  exact df_abstr _ _ _

theorem eq_X (u v w : Part A) (hu : u ⇓) (hv : v ⇓) (hw : w ⇓) :
    X ⬝ u ⬝ v ⬝ w = v ⬝ (u ⬝ u ⬝ v) ⬝ w := by
  unfold X
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu, eval_abstr_app _ _ _ _ hv, eval_abstr_app _ _ _ _ hw]
  change Part.some (v.get hv) ⬝ (Part.some (u.get hu) ⬝ Part.some (u.get hu) ⬝
    Part.some (v.get hv)) ⬝ Part.some (w.get hw) = v ⬝ (u ⬝ u ⬝ v) ⬝ w
  rw [Part.some_get hu, Part.some_get hv, Part.some_get hw]

/-- The call-by-name fixed-point combinator. -/
def Z : Part A := X ⬝ X

@[simp]
theorem df_Z : (Z : Part A) ⇓ := df_X_app X df_X

namespace Z

/-- The fixed-point combinator `Z` as a formal expression. -/
@[reducible]
def elm {Γ} : Expr Γ A := .elm (Z.get df_Z)

end Z

@[simp]
theorem df_Z_app (u : Part A) (hu : u ⇓) : (Z ⬝ u) ⇓ :=
  df_X_app_app X u df_X hu

theorem eq_Z (u v : Part A) (hu : u ⇓) (hv : v ⇓) : Z ⬝ u ⬝ v = u ⬝ (Z ⬝ u) ⬝ v := by
  change (X ⬝ X) ⬝ u ⬝ v = u ⬝ (X ⬝ X ⬝ u) ⬝ v
  rw [eq_X X u v df_X hu hv]

/-- Auxiliary combinator used to define the call-by-value fixed point combinator `Y`. -/
def W : Part A := [pca: ≪`x≫ ≪`y≫ .var `y ⬝ (.var `x ⬝ .var `x ⬝ .var `y)]

@[simp]
theorem df_W : (W : Part A) ⇓ := df_abstr _ _ _

@[simp]
theorem df_W_app (u : Part A) (hu : u ⇓) : (W ⬝ u) ⇓ := by
  unfold W
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu]
  exact df_abstr _ _ _

theorem eq_W (u v : Part A) (hu : u ⇓) (hv : v ⇓) :
    W ⬝ u ⬝ v = v ⬝ (u ⬝ u ⬝ v) := by
  unfold W
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu, eval_abstr_app _ _ _ _ hv]
  change Part.some (v.get hv) ⬝ (Part.some (u.get hu) ⬝
    Part.some (u.get hu) ⬝ Part.some (v.get hv)) = v ⬝ (u ⬝ u ⬝ v)
  rw [Part.some_get hu, Part.some_get hv]

/-- The call-by-value fixed-point combinator. -/
def Y : Part A := W ⬝ W

@[simp]
theorem df_Y : (Y : Part A) ⇓ := df_W_app W df_W

theorem eq_Y (u : Part A) (hu : u ⇓) : Y ⬝ u = u ⬝ (Y ⬝ u) := by
  change (W ⬝ W) ⬝ u = u ⬝ (W ⬝ W ⬝ u)
  nth_rw 1 [eq_W W u df_W hu]

/-! ### Curry numerals -/

/-- Curry numeral -/
def numeral : Nat → Part A
  | 0 => I
  | .succ n => pair ⬝ fal ⬝ (numeral n)

@[simp]
theorem df_numeral (n : Nat) : (numeral n : Part A) ⇓ := by
  induction n with
  | zero => exact df_I
  | succ n ih => exact df_pair_app_app fal _ df_fal ih

/-- The successor of a Curry numeral -/
def succ : Part A := pair ⬝ fal

@[simp]
theorem df_succ : (succ : Part A) ⇓ := df_pair_app fal df_fal

@[simp]
theorem df_succ_app (u : Part A) (hu : u ⇓) : (succ ⬝ u) ⇓ :=
  df_pair_app_app fal u df_fal hu

/-- Is a numeral equal to zero? -/
def iszero : Part A := fst

@[simp]
theorem eq_iszero_0 : iszero ⬝ (numeral 0) = (tru : Part A) := by
  change fst ⬝ I = tru
  rw [eq_fst I df_I]
  change I ⬝ K = K
  exact eq_I df_K₀

@[simp]
theorem eq_iszero_succ (n : Nat) : iszero ⬝ (numeral n.succ) = (fal : Part A) := by
  change fst ⬝ (pair ⬝ fal ⬝ numeral n) = fal
  rw [eq_fst_pair fal _ df_fal (df_numeral n)]

/-- Predecessor of a Curry numeral -/
def pred : Part A := [pca: ≪`x≫ (fst.elm ⬝ .var `x) ⬝ .I ⬝ (snd.elm ⬝ .var `x)]

@[simp]
theorem df_pred : (pred : Part A) ⇓ := df_abstr _ _ _

namespace pred

/-- The predecessor combinator as a formal expression. -/
@[reducible]
def elm {Γ} : Expr Γ A := .elm (pred.get df_pred)

end pred

namespace primrec

/-- Auxiliary combinator used in the definition of primitive recursion. -/
def R : Part A := [pca:
  ≪`r≫ ≪`x≫ ≪`f≫ ≪`m≫
    (fst.elm ⬝ .var `m) ⬝ (.K ⬝ .var `x) ⬝
    (≪ `y ≫ .var `f ⬝ (pred.elm ⬝ .var `m) ⬝
      (.var `r ⬝ .var `x ⬝ .var `f ⬝ (pred.elm ⬝ .var `m) ⬝ .I))
]

@[simp]
theorem df_R : (R : Part A) ⇓ := df_abstr _ _ _

namespace R

/-- The auxiliary combinator `primrec.R` as a formal expression. -/
def elm {Γ} : Expr Γ A := .elm (primrec.R.get primrec.df_R)

end R

end primrec

/-- Primitive recursion -/
def primrec : Part A :=
  [pca: ≪`x≫ ≪`f≫ ≪`m≫ (Z.elm ⬝ primrec.R.elm) ⬝ .var `x ⬝ .var `f ⬝ .var `m ⬝ .I]

end PCA

end LeanPool.PartialCombinatoryAlgebras
