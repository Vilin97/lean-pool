/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.CloseRotate
import LeanPool.RegtsSevenster.RS.Novel.Skein.InterfaceShift
import LeanPool.RegtsSevenster.RS.Novel.Skein.PairCloseComm
import LeanPool.RegtsSevenster.RS.Novel.Skein.IdentityLaw
import LeanPool.RegtsSevenster.RS.Novel.Skein.Trace

/-!
# Cyclicity of the trace

The trace of a composition is independent of the order
(`fragTrace_comm`, accompanying paper, Lemma 3.5(a)): closing
`F ∘ G` by the strand bundle and closing `G ∘ F` by the strand
bundle produce isomorphic closed fragments.  Both reduce, by the rotation
(`pairCloseComposeRotate`) and the identity law
(`composeStrandBundleLeft`), to the closure of `F` against a
transposed copy of `G`; the two reductions are matched by the
commutativity of the closure and the closure-relabel exchange
(`pairCloseRelabel`), itself derived from `interfaceShift` at
`s = 0`, where the outgoing block is the entire boundary.
-/

namespace RS

/-- The inverse of the transpose is the reverse transpose. -/
theorem transposeEquiv_symm (n p : ℕ) :
    (transposeEquiv n p).symm = transposeEquiv p n := by
  apply _root_.Equiv.ext
  intro x
  by_cases hx : x.val < p
  · rw [show x = (⟨x.val, x.isLt⟩ : Fin (p + n)) from Fin.ext rfl,
      transposeEquiv_symm_low n p x.val hx,
      transposeEquiv_low p n x.val hx]
    all_goals omega
  · have hj : x.val - p < n := by have := x.isLt; omega
    rw [show x = (⟨p + (x.val - p), by have := x.isLt; omega⟩ :
        Fin (p + n)) from Fin.ext
          (by change x.val = p + (x.val - p); omega),
      transposeEquiv_symm_high n p (x.val - p) hj,
      transposeEquiv_high p n (x.val - p) hj]
    all_goals omega

/-- The closure respects fragment equivalence in both slots. -/
noncomputable def pairCloseCongr {t : ℕ}
    {F₁ F₂ G₁ G₂ : Fragment (Fin t)}
    (hF : F₁.Equiv F₂) (hG : G₁.Equiv G₂) :
    (pairClose F₁ G₁).Equiv (pairClose F₂ G₂) :=
  Fragment.composeCongr
    (Fragment.Equiv.relabelCongr hF _)
    (Fragment.Equiv.relabelCongr hG _)

/-- Label algebra: post-composing a boundary permutation with the
low cast is pre-composing the cast with the outgoing permutation
at `s = 0`. -/
theorem cast_trans_outPerm {t : ℕ} (e : Equiv.Perm (Fin t)) :
    e.trans (finCongr (by omega : t = 0 + t)) =
      (finCongr (by omega : t = 0 + t)).trans (outPermEquiv 0 e) := by
  apply _root_.Equiv.ext
  intro j
  simp only [_root_.Equiv.trans_apply]
  rw [show (finCongr (by omega : t = 0 + t) j : Fin (0 + t)) =
      Fin.natAdd 0 j from Fin.ext (by change j.val = 0 + j.val; omega),
    outPermEquiv_high 0 e j]
  exact Fin.ext (by change (e j).val = 0 + (e j).val; omega)

/-- Label algebra: post-composing the inverse boundary permutation
with the high cast is pre-composing the cast with the incoming
permutation at `u = 0`. -/
theorem cast_trans_inPerm {t : ℕ} (e : Equiv.Perm (Fin t)) :
    e.symm.trans (finCongr (by omega : t = t + 0)) =
      (finCongr (by omega : t = t + 0)).trans
        (inPermEquiv e.symm 0) := by
  apply _root_.Equiv.ext
  intro j
  simp only [_root_.Equiv.trans_apply]
  rw [show (finCongr (by omega : t = t + 0) j : Fin (t + 0)) =
      Fin.castAdd 0 j from Fin.ext rfl,
    inPermEquiv_low e.symm 0 j]
  exact Fin.ext rfl

/-- The closure-relabel exchange for boundary permutations:
relabelling the first factor of a closure by a permutation is
relabelling the second by the inverse.  Instance of
`interfaceShift` at `s = 0`, where the outgoing block is the
whole boundary. -/
noncomputable def pairCloseRelabelPerm {t : ℕ}
    (e : Equiv.Perm (Fin t)) (X Y : Fragment (Fin t)) :
    (pairClose (X.relabel e) Y).Equiv
      (pairClose X (Y.relabel e.symm)) :=
  (Fragment.composeCongr
      ((Fragment.Equiv.relabelTrans X e
          (finCongr (by omega : t = 0 + t))).trans
        ((Fragment.Equiv.relabelEq X (cast_trans_outPerm e)).trans
          (Fragment.Equiv.relabelTrans X
            (finCongr (by omega : t = 0 + t))
            (outPermEquiv 0 e)).symm))
      (Fragment.Equiv.refl
        (Y.relabel (finCongr (by omega : t = t + 0))))).trans
    ((interfaceShift e
        (X.relabel (finCongr (by omega : t = 0 + t)))
        (Y.relabel (finCongr (by omega : t = t + 0)))).trans
      (Fragment.composeCongr
        (Fragment.Equiv.refl
          (X.relabel (finCongr (by omega : t = 0 + t))))
        ((Fragment.Equiv.relabelTrans Y
            (finCongr (by omega : t = t + 0))
            (inPermEquiv e.symm 0)).trans
          ((Fragment.Equiv.relabelEq Y
              (cast_trans_inPerm e).symm).trans
            (Fragment.Equiv.relabelTrans Y e.symm
              (finCongr (by omega : t = t + 0))).symm))))

/-- The closure-relabel exchange across a pure cast. -/
noncomputable def pairCloseCast {a b : ℕ} (h : a = b)
    (X : Fragment (Fin a)) (Y : Fragment (Fin b)) :
    (pairClose (X.relabel (finCongr h)) Y).Equiv
      (pairClose X (Y.relabel (finCongr h.symm))) := by
  subst h
  exact pairCloseCongr
    (Fragment.Equiv.relabelRefl X)
    (Fragment.Equiv.relabelRefl Y).symm

/-- **The closure-relabel exchange**: relabelling the first factor
of a closure is relabelling the second factor by the inverse
label equivalence. -/
noncomputable def pairCloseRelabel {a b : ℕ} (e : Fin a ≃ Fin b)
    (X : Fragment (Fin a)) (Y : Fragment (Fin b)) :
    (pairClose (X.relabel e) Y).Equiv
      (pairClose X (Y.relabel e.symm)) := by
  have h : a = b := by simpa using Fintype.card_congr e
  have hsplit : e = (finCongr h).trans
      ((finCongr h).symm.trans e) :=
    _root_.Equiv.ext fun _ => rfl
  have hsymm : (((finCongr h).symm.trans e).symm.trans
      (finCongr h.symm)) = e.symm :=
    _root_.Equiv.ext fun _ => rfl
  exact (pairCloseCongr
      ((Fragment.Equiv.relabelEq X hsplit).trans
        (Fragment.Equiv.relabelTrans X (finCongr h)
          ((finCongr h).symm.trans e)).symm)
      (Fragment.Equiv.refl Y)).trans
    ((pairCloseRelabelPerm ((finCongr h).symm.trans e)
        (X.relabel (finCongr h)) Y).trans
      ((pairCloseCast h X
          (Y.relabel ((finCongr h).symm.trans e).symm)).trans
        (pairCloseCongr (Fragment.Equiv.refl X)
          ((Fragment.Equiv.relabelTrans Y
              ((finCongr h).symm.trans e).symm
              (finCongr h.symm)).trans
            (Fragment.Equiv.relabelEq Y hsymm)))))

/-- **Cyclicity of the trace** (accompanying paper, Lemma 3.5(a)):
for an
isomorphism-invariant parameter, the trace of a composition does
not depend on the order of the factors. -/
theorem fragTrace_comm (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {t u : ℕ} (F : Fragment (Fin (t + u)))
    (G : Fragment (Fin (u + t))) :
    fragTrace f (F.compose G) = fragTrace f (G.compose F) := by
  have E1 : (pairClose (F.compose G) (strandBundle t)).Equiv
      (pairClose F (G.relabel (transposeEquiv u t))) :=
    (pairCloseComposeRotate F G (strandBundle t)).trans
      (pairCloseCongr (Fragment.Equiv.refl F)
        (composeStrandBundleLeft t u
          (G.relabel (transposeEquiv u t))))
  have E2 : (pairClose (G.compose F) (strandBundle u)).Equiv
      (pairClose F (G.relabel (transposeEquiv u t))) :=
    (pairCloseComposeRotate G F (strandBundle u)).trans
      ((pairCloseCongr (Fragment.Equiv.refl G)
          (composeStrandBundleLeft u t
            (F.relabel (transposeEquiv t u)))).trans
        ((Fragment.pairCloseComm G
            (F.relabel (transposeEquiv t u))).trans
          ((pairCloseRelabel (transposeEquiv t u) F G).trans
            (pairCloseCongr (Fragment.Equiv.refl F)
              (Fragment.Equiv.relabelEq G
                (transposeEquiv_symm t u))))))
  unfold fragTrace
  rw [hf _ _ E1, hf _ _ E2]

end RS
