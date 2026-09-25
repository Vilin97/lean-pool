/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.SkeinPowBraid
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.AdjacentWord

/-!
# The skein braiding as a bundle map

The skein-side adjacent braiding collapses to the bundle-map
class of the adjacent transposition: the whiskers are block sums
of label equivalences and the one-strand braiding is the
transpose, so the whole recursion lives in the bundle-map
calculus.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

/-- The adjacent swap as a label equivalence. -/
def adjSwapEquiv (n i : ℕ) (h : i + 2 ≤ n) : Fin n ≃ Fin n :=
  _root_.Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩

/-- The value of a swap, on underlying values. -/
theorem swap_val {m : ℕ} (a b x : Fin m) :
    ((_root_.Equiv.swap a b) x).val =
      if x.val = a.val then b.val
      else if x.val = b.val then a.val else x.val := by
  rw [_root_.Equiv.swap_apply_def]
  by_cases h1 : x = a
  · rw [ite_eq_left h1, ite_eq_left (by rw [h1])]
  · rw [ite_eq_right h1, ite_eq_right (fun hv => h1 (Fin.ext hv))]
    by_cases h2 : x = b
    · rw [ite_eq_left h2, ite_eq_left (by rw [h2])]
    · rw [ite_eq_right h2, ite_eq_right (fun hv => h2 (Fin.ext hv))]

/-- The value of the adjacent swap. -/
theorem adjSwapEquiv_val (n i : ℕ) (h : i + 2 ≤ n)
    (x : Fin n) :
    ((adjSwapEquiv n i h) x).val =
      if x.val = i then i + 1
      else if x.val = i + 1 then i else x.val :=
  swap_val _ _ x

/-- The top block sum is the adjacent swap. -/
theorem tensorMapEquiv_top (n : ℕ) :
    tensorMapEquiv (_root_.Equiv.refl (Fin n))
        (transposeEquiv 1 1) =
      adjSwapEquiv (n + 2) n (by omega) := by
  refine _root_.Equiv.ext (fun x => Fin.ext ?_)
  rw [adjSwapEquiv_val]
  rcases Nat.lt_or_ge x.val n with hx | hx
  · conv_lhs => rw [show x = Fin.castAdd 2 ⟨x.val, hx⟩ from
      Fin.ext rfl, tensorMapEquiv_castAdd]
    change x.val = _
    rw [ite_eq_right (show ¬ (x.val = n) by omega),
      ite_eq_right (show ¬ (x.val = n + 1) by omega)]
  · have hx2 := x.isLt
    rcases (show x.val = n ∨ x.val = n + 1 by omega)
      with hv | hv
    · conv_lhs => rw [show x = Fin.natAdd n ⟨0, by omega⟩ from
        Fin.ext (by change x.val = n + 0; omega),
        tensorMapEquiv_natAdd,
        show transposeEquiv 1 1 ⟨0, by omega⟩ =
            ⟨1 + 0, by omega⟩ from
          transposeEquiv_low 1 1 0 (by omega) _ _]
      change n + (1 + 0) = _
      rw [ite_eq_left hv]
    · conv_lhs => rw [show x = Fin.natAdd n ⟨1, by omega⟩ from
        Fin.ext (by change x.val = n + 1; omega),
        tensorMapEquiv_natAdd,
        show transposeEquiv 1 1 ⟨1, by omega⟩ =
            ⟨0, by omega⟩ from by
          rw [show (⟨1, by omega⟩ : Fin (1 + 1)) =
            ⟨1 + 0, by omega⟩ from Fin.ext rfl]
          exact transposeEquiv_high 1 1 0 (by omega) _ _]
      change n + 0 = _
      rw [ite_eq_right (show ¬ (x.val = n) by omega), ite_eq_left hv]
      omega

/-- The whiskered block sum is the shifted adjacent swap. -/
theorem tensorMapEquiv_whisker (n i : ℕ) (h : i + 2 ≤ n + 1) :
    tensorMapEquiv (adjSwapEquiv (n + 1) i h)
        (_root_.Equiv.refl (Fin 1)) =
      adjSwapEquiv (n + 2) i (by omega) := by
  refine _root_.Equiv.ext (fun x => Fin.ext ?_)
  rw [adjSwapEquiv_val]
  rcases Nat.lt_or_ge x.val (n + 1) with hx | hx
  · conv_lhs => rw [show x = Fin.castAdd 1 ⟨x.val, hx⟩ from
      Fin.ext rfl, tensorMapEquiv_castAdd]
    change ((adjSwapEquiv (n + 1) i h) ⟨x.val, hx⟩).val = _
    rw [adjSwapEquiv_val]
  · have hx2 := x.isLt
    have hv : x.val = n + 1 := by omega
    conv_lhs => rw [show x = Fin.natAdd (n + 1) ⟨0, by omega⟩
      from Fin.ext (by change x.val = n + 1 + 0; omega),
      tensorMapEquiv_natAdd]
    change n + 1 + 0 = _
    rw [ite_eq_right (show ¬ (x.val = i) by omega),
      ite_eq_right (show ¬ (x.val = i + 1) by omega)]
    omega

variable {R : ℕ} (f : EdgeRankParameter R)

/-- **The skein adjacent braiding is the adjacent-swap bundle
map.** -/
theorem skeinPowBraid_bmc :
    ∀ (n i : ℕ) (h : i + 2 ≤ n),
      skeinPowBraid f n i h =
        bundleMapClass f (adjSwapEquiv n i h)
  | 0, _, h => absurd h (by omega)
  | 1, _, h => absurd h (by omega)
  | n + 2, i, h => by
    by_cases hi : i = n
    · rw [show skeinPowBraid f (n + 2) i h =
          (SkeinObj.mk n : SkeinObj f) ◁
            (β_ (SkeinObj.mk 1 : SkeinObj f)
              (SkeinObj.mk 1)).hom from dite_eq_left hi]
      change HomSpace.tensor f n n 2 2
          (HomSpace.ofFragment f.val (strandBundle n))
          (bundleMapClass f (transposeEquiv 1 1)) = _
      rw [bundleMapClass_tensor_id_left, tensorMapEquiv_top]
      exact bundleMapClass_congr f (by subst hi; rfl)
    · have hle : i + 2 ≤ n + 1 := by omega
      rw [show skeinPowBraid f (n + 2) i h =
          (skeinPowBraid f (n + 1) i hle) ▷ SkeinObj.mk 1 from
        dite_eq_right hi]
      rw [skeinPowBraid_bmc (n + 1) i hle]
      change HomSpace.tensor f (n + 1) (n + 1) 1 1
          (bundleMapClass f (adjSwapEquiv (n + 1) i hle))
          (HomSpace.ofFragment f.val (strandBundle 1)) = _
      rw [bundleMapClass_tensor_id_right,
        tensorMapEquiv_whisker]

end RS
