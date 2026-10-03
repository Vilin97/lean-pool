/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.ArbitraryWeakPoissonJets

/-!
# Elliptic bootstrap with a smooth zeroth-order coefficient

Adapted from AlmostSchur/ArbitraryWeakPoissonJets.lean in
Arthur742Ramos/lean-poincare-formalization-plan at immutable commit
3faf25aefc27842a77c37ca178e8a40a20bb20c7. The original coefficient,
difference-quotient and extraction arguments are reused with attribution.
This adaptation adds multiplication by a derivative of the smooth potential
and changes the base forcing from F to F times the root weak jet.
Consequently F is a smooth coefficient; the unknown function is never
assumed smooth. The equation is div(A grad u) = F u.

This file proves local Euclidean steps. Manifold assembly is separate.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter AlmostSchur
open scoped Topology ContDiff BigOperators Convolution Pointwise Matrix.Norms.Elementwise
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness

namespace LichnerowiczObata.Reaction
universe uE uι

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩

private theorem weak_derivative_add
    {K : Set E} {v : E} {u du w dw : E → ℝ}
    (hu : MemLp u 2 (volume.restrict K))
    (hdu : MemLp du 2 (volume.restrict K))
    (hw : MemLp w 2 (volume.restrict K))
    (hdw : MemLp dw 2 (volume.restrict K))
    (h₁ : HasWeakDirectionalDerivativeOn K v u du)
    (h₂ : HasWeakDirectionalDerivativeOn K v w dw) :
    HasWeakDirectionalDerivativeOn K v (fun z => u z + w z)
      (fun z => du z + dw z) := by
  intro φ hφ hc hs
  have hφm : MemLp φ 2 (volume.restrict K) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc : MemLp φ 2 volume).restrict K
  have hφd : MemLp (fun z => fderiv ℝ φ z v) 2 (volume.restrict K) :=
    ((contDiff_smooth_test_derivative hφ v).continuous.memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ v) : MemLp _ 2 volume).restrict K
  have hleft : (∫ z in K, (u z + w z) * fderiv ℝ φ z v) =
      (∫ z in K, u z * fderiv ℝ φ z v) +
        ∫ z in K, w z * fderiv ℝ φ z v := by
    calc
      _ = ∫ z in K, u z * fderiv ℝ φ z v + w z * fderiv ℝ φ z v := by
        congr 1
        funext z
        ring
      _ = _ := integral_add (hu.integrable_mul hφd) (hw.integrable_mul hφd)
  have hright : (∫ z in K, (du z + dw z) * φ z) =
      (∫ z in K, du z * φ z) + ∫ z in K, dw z * φ z := by
    calc
      _ = ∫ z in K, du z * φ z + dw z * φ z := by
        congr 1
        funext z
        ring
      _ = _ := integral_add (hdu.integrable_mul hφm) (hdw.integrable_mul hφm)
  rw [hleft, hright, h₁ φ hφ hc hs, h₂ φ hφ hc hs]
  ring

private theorem weak_derivative_sub
    {K : Set E} {v : E} {u du w dw : E → ℝ}
    (hu : MemLp u 2 (volume.restrict K))
    (hdu : MemLp du 2 (volume.restrict K))
    (hw : MemLp w 2 (volume.restrict K))
    (hdw : MemLp dw 2 (volume.restrict K))
    (h₁ : HasWeakDirectionalDerivativeOn K v u du)
    (h₂ : HasWeakDirectionalDerivativeOn K v w dw) :
    HasWeakDirectionalDerivativeOn K v (fun z => u z - w z)
      (fun z => du z - dw z) := by
  intro φ hφ hc hs
  have hφm : MemLp φ 2 (volume.restrict K) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc : MemLp φ 2 volume).restrict K
  have hφd : MemLp (fun z => fderiv ℝ φ z v) 2 (volume.restrict K) :=
    ((contDiff_smooth_test_derivative hφ v).continuous.memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ v) : MemLp _ 2 volume).restrict K
  have hleft : (∫ z in K, (u z - w z) * fderiv ℝ φ z v) =
      (∫ z in K, u z * fderiv ℝ φ z v) -
        ∫ z in K, w z * fderiv ℝ φ z v := by
    calc
      _ = ∫ z in K, u z * fderiv ℝ φ z v - w z * fderiv ℝ φ z v := by
        congr 1
        funext z
        ring
      _ = _ := integral_sub (hu.integrable_mul hφd) (hw.integrable_mul hφd)
  have hright : (∫ z in K, (du z - dw z) * φ z) =
      (∫ z in K, du z * φ z) - ∫ z in K, dw z * φ z := by
    calc
      _ = ∫ z in K, du z * φ z - dw z * φ z := by
        congr 1
        funext z
        ring
      _ = _ := integral_sub (hdu.integrable_mul hφm) (hdw.integrable_mul hφm)
  rw [hleft, hright, h₁ φ hφ hc hs, h₂ φ hφ hc hs]
  ring



inductive ReactionExpr {ι : Type uι} {K : Set E} {n : ℕ}
    (b : ι → E) (J : LocalL2DerivativeJet b K n)
    (A : E → ι → ι → ℝ) (F : E → ℝ) : Type (max uE uι)
  | zero
  | smoothF (w : List ι)
  | coeff (i j : ι) (w : List ι)
  | jet (w : List ι)
  | add (p q : ReactionExpr b J A F)
  | sub (p q : ReactionExpr b J A F)
  | coeffMul (i j : ι) (w : List ι) (p : ReactionExpr b J A F)
  | potentialMul (w : List ι) (p : ReactionExpr b J A F)
  | sum (p : ι → ReactionExpr b J A F)

namespace ReactionExpr

variable {ι : Type uι} [Fintype ι] {K : Set E} {n : ℕ}
  {b : ι → E} {J : LocalL2DerivativeJet b K n}
  {A : E → ι → ι → ℝ} {F : E → ℝ}

def eval : ReactionExpr b J A F → E → ℝ
  | .zero => fun _ => 0
  | .smoothF w => localDirectionalIterate b F w
  | .coeff i j w => localDirectionalIterate b (fun z => A z i j) w
  | .jet w => fun z => J.value w z
  | .add p q => fun z => eval p z + eval q z
  | .sub p q => fun z => eval p z - eval q z
  | .coeffMul i j w p => fun z =>
      localDirectionalIterate b (fun y => A y i j) w z * eval p z
  | .potentialMul w p => fun z =>
      localDirectionalIterate b F w z * eval p z
  | .sum p => fun z => ∑ i, eval (p i) z

def jetBound : ReactionExpr b J A F → ℕ
  | .zero => 0
  | .smoothF _ => 0
  | .coeff _ _ _ => 0
  | .jet w => w.length
  | .add p q => max (jetBound p) (jetBound q)
  | .sub p q => max (jetBound p) (jetBound q)
  | .coeffMul _ _ _ p => jetBound p
  | .potentialMul _ p => jetBound p
  | .sum p => Finset.sup Finset.univ (fun i => jetBound (p i))

def deriv (k : ι) : ReactionExpr b J A F → ReactionExpr b J A F
  | .zero => .zero
  | .smoothF w => .smoothF (k :: w)
  | .coeff i j w => .coeff i j (k :: w)
  | .jet w => .jet (k :: w)
  | .add p q => .add (deriv k p) (deriv k q)
  | .sub p q => .sub (deriv k p) (deriv k q)
  | .coeffMul i j w p =>
      .add (.coeffMul i j (k :: w) p) (.coeffMul i j w (deriv k p))
  | .potentialMul w p =>
      .add (.potentialMul (k :: w) p) (.potentialMul w (deriv k p))
  | .sum p => .sum (fun i => deriv k (p i))

def commutator (w : List ι) (k : ι) : ReactionExpr b J A F :=
  .sum (fun j => .sum (fun i =>
    .add (.coeffMul i j [j, k] (.jet (i :: w)))
      (.coeffMul i j [k] (.jet (j :: i :: w)))))

def forcing : List ι → ReactionExpr b J A F
  | [] => .potentialMul [] (.jet [])
  | k :: w => .sub (deriv k (forcing w)) (commutator w k)

private theorem jetBound_sum_le (p : ι → ReactionExpr b J A F) (i : ι) :
    jetBound (p i) ≤ jetBound (.sum p) := by
  change jetBound (p i) ≤ Finset.sup Finset.univ (fun j => jetBound (p j))
  exact Finset.le_sup (s := Finset.univ) (f := fun j => jetBound (p j))
    (b := i) (Finset.mem_univ i)

theorem jetBound_deriv_le (k : ι) (p : ReactionExpr b J A F) :
    jetBound (deriv k p) ≤ jetBound p + 1 := by
  induction p generalizing k with
  | zero => simp [deriv, jetBound]
  | smoothF w => simp [deriv, jetBound]
  | coeff i j w => simp [deriv, jetBound]
  | jet w => simp [deriv, jetBound]
  | add p q hp hq =>
      simp only [deriv, jetBound]
      exact max_le ((hp k).trans (Nat.add_le_add_right (le_max_left _ _) 1))
        ((hq k).trans (Nat.add_le_add_right (le_max_right _ _) 1))
  | sub p q hp hq =>
      simp only [deriv, jetBound]
      exact max_le ((hp k).trans (Nat.add_le_add_right (le_max_left _ _) 1))
        ((hq k).trans (Nat.add_le_add_right (le_max_right _ _) 1))
  | coeffMul i j w p hp =>
      simp only [deriv, jetBound]
      exact max_le (Nat.le_add_right _ _)
        (hp k)
  | potentialMul w p hp =>
      simp only [deriv, jetBound]
      exact max_le (Nat.le_add_right _ _)
        (hp k)
  | sum p ih =>
      simp only [deriv, jetBound]
      apply Finset.sup_le
      intro i hi
      exact (ih i k).trans (Nat.add_le_add_right (jetBound_sum_le p i) 1)

theorem jetBound_commutator_le (w : List ι) (k : ι) :
  jetBound (commutator (b := b) (J := J) (A := A) (F := F) w k) ≤
      w.length + 2 := by
  unfold commutator
  apply Finset.sup_le
  intro j hj
  apply Finset.sup_le
  intro i hi
  simp only [jetBound]
  exact max_le (by simp) (by simp)

theorem jetBound_forcing_le (w : List ι) :
    jetBound (forcing (b := b) (J := J) (A := A) (F := F) w) ≤
      w.length + 1 := by
  induction w with
  | nil => simp [forcing, jetBound]
  | cons k w ih =>
      simp only [forcing, jetBound]
      exact max_le
        ((jetBound_deriv_le k _).trans (Nat.add_le_add_right ih 1))
        (jetBound_commutator_le w k)

end ReactionExpr

namespace ReactionExpr

variable {ι : Type uι} [Fintype ι] {K : Set E} {n : ℕ}
  {b : ι → E} {J : LocalL2DerivativeJet b K n}
  {A : E → ι → ι → ℝ} {F : E → ℝ}

theorem memLp_eval
    (hK : IsCompact K) {W : Set E} (hW : IsOpen W) (hKW : K ⊆ W)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) W)
    (hF : ContDiffOn ℝ ∞ F W)
    (p : ReactionExpr b J A F) (hp : p.jetBound ≤ n) :
    MemLp (p.eval) 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  induction p with
  | zero => simpa [eval] using (memLp_const (μ := volume.restrict K) (p := 2) (0 : ℝ))
  | smoothF w =>
      simpa [eval] using memLp_localDirectionalIterate_on_compact b hK hW hKW hF w
  | coeff i j w =>
      simpa [eval] using
        memLp_localDirectionalIterate_on_compact b hK hW hKW (hA i j) w
  | jet w =>
      simpa [eval] using (Lp.memLp (J.value w)).restrict K
  | add p q ihp ihq =>
      have hp' : p.jetBound ≤ n := le_trans (le_max_left _ _) hp
      have hq' : q.jetBound ≤ n := le_trans (le_max_right _ _) hp
      change MemLp (p.eval + q.eval) 2 (volume.restrict K)
      exact (ihp hp').add (ihq hq')
  | sub p q ihp ihq =>
      have hp' : p.jetBound ≤ n := le_trans (le_max_left _ _) hp
      have hq' : q.jetBound ≤ n := le_trans (le_max_right _ _) hp
      change MemLp (p.eval - q.eval) 2 (volume.restrict K)
      exact (ihp hp').sub (ihq hq')
  | coeffMul i j w p ih =>
      simpa [eval] using memLp_mul_coefficient_on_compact hK
        ((contDiffOn_localDirectionalIterate b hW (hA i j) w).continuousOn.mono hKW)
        (ih hp)
  | potentialMul w p ih =>
      simpa [eval] using memLp_mul_coefficient_on_compact hK
        ((contDiffOn_localDirectionalIterate b hW hF w).continuousOn.mono hKW)
        (ih hp)
  | sum p ih =>
      simpa [eval] using
        (memLp_finsetSum Finset.univ (fun i hi =>
          ih i (le_trans (jetBound_sum_le p i) hp)))

theorem weak_derivative_eval
    (hK : IsCompact K) {W : Set E} (hW : IsOpen W) (hKW : K ⊆ W)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) W)
    (hF : ContDiffOn ℝ ∞ F W)
    (p : ReactionExpr b J A F) (hp : p.jetBound + 1 ≤ n) (k : ι) :
    HasWeakDirectionalDerivativeOn K (b k) p.eval (deriv k p).eval := by
  induction p generalizing k with
  | zero =>
      intro φ hφ hc hs
      simp [eval, deriv]
  | smoothF w =>
      simpa [eval, deriv, localDirectionalIterate] using
        hasWeakDirectionalDerivativeOn_localDirectionalIterate b hW hKW hF w k
  | coeff i j w =>
      simpa [eval, deriv] using
        hasWeakDirectionalDerivativeOn_localDirectionalIterate b hW hKW (hA i j) w k
  | jet w =>
      have hw : w.length < n := by
        simpa [jetBound] using hp
      simpa [eval, deriv] using J.weak w hw k
  | add p q ihp ihq =>
      have hp' : p.jetBound + 1 ≤ n := by
        exact le_trans (Nat.add_le_add_right (le_max_left _ _) 1) (by simpa [jetBound] using hp)
      have hq' : q.jetBound + 1 ≤ n := by
        exact le_trans (Nat.add_le_add_right (le_max_right _ _) 1) (by simpa [jetBound] using hp)
      simpa [eval, deriv] using weak_derivative_add
        (memLp_eval hK hW hKW hA hF p (Nat.le_of_succ_le hp'))
        (memLp_eval hK hW hKW hA hF (deriv k p)
          ((jetBound_deriv_le k p).trans hp'))
        (memLp_eval hK hW hKW hA hF q (Nat.le_of_succ_le hq'))
        (memLp_eval hK hW hKW hA hF (deriv k q)
          ((jetBound_deriv_le k q).trans hq'))
        (ihp hp' k) (ihq hq' k)
  | sub p q ihp ihq =>
      have hp' : p.jetBound + 1 ≤ n := by
        exact le_trans (Nat.add_le_add_right (le_max_left _ _) 1) (by simpa [jetBound] using hp)
      have hq' : q.jetBound + 1 ≤ n := by
        exact le_trans (Nat.add_le_add_right (le_max_right _ _) 1) (by simpa [jetBound] using hp)
      simpa [eval, deriv] using weak_derivative_sub
        (memLp_eval hK hW hKW hA hF p (Nat.le_of_succ_le hp'))
        (memLp_eval hK hW hKW hA hF (deriv k p)
          ((jetBound_deriv_le k p).trans hp'))
        (memLp_eval hK hW hKW hA hF q (Nat.le_of_succ_le hq'))
        (memLp_eval hK hW hKW hA hF (deriv k q)
          ((jetBound_deriv_le k q).trans hq'))
        (ihp hp' k) (ihq hq' k)
  | coeffMul i j w p ih =>
      have hp1 : p.jetBound + 1 ≤ n := by simpa [jetBound] using hp
      have hp0 : p.jetBound ≤ n := Nat.le_of_succ_le hp1
      simpa [eval, deriv, localDirectionalIterate] using
        HasWeakDirectionalDerivativeOn.mul_coefficient hW hKW
          (memLp_eval hK hW hKW hA hF p hp0)
          (memLp_eval hK hW hKW hA hF (deriv k p)
            (le_trans (jetBound_deriv_le k p) hp1))
          (ih hp1 k)
          (contDiffOn_localDirectionalIterate b hW (hA i j) w)
  | potentialMul w p ih =>
      have hp1 : p.jetBound + 1 ≤ n := by simpa [jetBound] using hp
      have hp0 : p.jetBound ≤ n := Nat.le_of_succ_le hp1
      simpa [eval, deriv, localDirectionalIterate] using
        HasWeakDirectionalDerivativeOn.mul_coefficient hW hKW
          (memLp_eval hK hW hKW hA hF p hp0)
          (memLp_eval hK hW hKW hA hF (deriv k p)
            (le_trans (jetBound_deriv_le k p) hp1))
          (ih hp1 k)
          (contDiffOn_localDirectionalIterate b hW hF w)
  | sum p ih =>
      simpa [eval, deriv] using
        (HasWeakDirectionalDerivativeOn.finset_sum Finset.univ
          (fun i => (p i).eval) (fun i => (deriv k (p i)).eval)
          (fun i hi => memLp_eval hK hW hKW hA hF (p i)
            (Nat.le_of_succ_le (le_trans
              (Nat.add_le_add_right (jetBound_sum_le p i) 1) hp)))
          (fun i hi => memLp_eval hK hW hKW hA hF (deriv k (p i))
            ((jetBound_deriv_le k (p i)).trans (le_trans
              (Nat.add_le_add_right (jetBound_sum_le p i) 1) hp)))
          (fun i hi => ih i (le_trans
            (Nat.add_le_add_right (jetBound_sum_le p i) 1) hp) k))

end ReactionExpr

namespace ReactionExpr

variable {ι : Type*} [Fintype ι] {K K' : Set E} {n : ℕ}
  {b : ι → E} {J : LocalL2DerivativeJet b K n}
  {J' : LocalL2DerivativeJet b K' n}
  {A : E → ι → ι → ℝ} {F : E → ℝ}

/-- Reindex an expression along a replacement of its weak jet.  The
expression tree is unchanged; only the jet used by its evaluation changes. -/
def reindex : ReactionExpr b J A F → ReactionExpr b J' A F
  | .zero => .zero
  | .smoothF w => .smoothF w
  | .coeff i j w => .coeff i j w
  | .jet w => .jet w
  | .add p q => .add (reindex p) (reindex q)
  | .sub p q => .sub (reindex p) (reindex q)
  | .coeffMul i j w p => .coeffMul i j w (reindex p)
  | .potentialMul w p => .potentialMul w (reindex p)
  | .sum p => .sum (fun i => reindex (p i))

theorem jetBound_reindex (p : ReactionExpr b J A F) :
    jetBound (reindex (J' := J') p) = jetBound p := by
  induction p with
  | zero | smoothF _ | coeff _ _ _ | jet _ => rfl
  | add p q hp hq => simp [reindex, jetBound, hp, hq]
  | sub p q hp hq => simp [reindex, jetBound, hp, hq]
  | coeffMul i j w p hp => simp [reindex, jetBound, hp]
  | potentialMul w p hp => simp [reindex, jetBound, hp]
  | sum p ih =>
      simp only [reindex, jetBound]
      congr 1
      funext i
      exact ih i

theorem eval_reindex_eq
    (p : ReactionExpr b J A F)
    (hJ : ∀ w : List ι, w.length ≤ n → J.value w = J'.value w)
    (hp : p.jetBound ≤ n) :
    p.eval = (reindex (J' := J') p).eval := by
  induction p with
  | zero => rfl
  | smoothF _ => rfl
  | coeff _ _ _ => rfl
  | jet w =>
      have hw : w.length ≤ n := by simpa [jetBound] using hp
      simpa [eval, reindex] using congrArg
        (fun z : Lp ℝ 2 (volume : Measure E) => (z : E → ℝ)) (hJ w hw)
  | add p q ihp ihq =>
      have hp' : p.jetBound ≤ n := le_trans (le_max_left _ _) hp
      have hq' : q.jetBound ≤ n := le_trans (le_max_right _ _) hp
      funext z
      simp only [eval, reindex]
      rw [congrFun (ihp hp') z, congrFun (ihq hq') z]
  | sub p q ihp ihq =>
      have hp' : p.jetBound ≤ n := le_trans (le_max_left _ _) hp
      have hq' : q.jetBound ≤ n := le_trans (le_max_right _ _) hp
      funext z
      simp only [eval, reindex]
      rw [congrFun (ihp hp') z, congrFun (ihq hq') z]
  | coeffMul i j w p ih =>
      have hp' : p.jetBound ≤ n := by simpa [jetBound] using hp
      funext z
      simp only [eval, reindex]
      rw [congrFun (ih hp') z]
  | potentialMul w p ih =>
      have hp' : p.jetBound ≤ n := by simpa [jetBound] using hp
      funext z
      simp only [eval, reindex]
      rw [congrFun (ih hp') z]
  | sum p ih =>
      funext z
      simp only [eval, reindex]
      apply Finset.sum_congr rfl
      intro i hi
      exact congrFun (ih i (le_trans (jetBound_sum_le p i) hp)) z

theorem eval_reindex_eq_all
    (p : ReactionExpr b J A F)
    (hJ : ∀ w : List ι, J.value w = J'.value w) :
    p.eval = (reindex (J' := J') p).eval := by
  induction p with
  | zero => rfl
  | smoothF _ => rfl
  | coeff _ _ _ => rfl
  | jet w =>
      simpa [eval, reindex] using congrArg
        (fun z : Lp ℝ 2 (volume : Measure E) => (z : E → ℝ)) (hJ w)
  | add p q ihp ihq =>
      funext z
      simp only [eval, reindex]
      rw [congrFun ihp z, congrFun ihq z]
  | sub p q ihp ihq =>
      funext z
      simp only [eval, reindex]
      rw [congrFun ihp z, congrFun ihq z]
  | coeffMul i j w p ih =>
      funext z
      simp only [eval, reindex]
      rw [congrFun ih z]
  | potentialMul w p ih =>
      funext z
      simp only [eval, reindex]
      rw [congrFun ih z]
  | sum p ih =>
      funext z
      simp only [eval, reindex]
      apply Finset.sum_congr rfl
      intro i hi
      exact congrFun (ih i) z

theorem reindex_deriv (k : ι) (p : ReactionExpr b J A F) :
    reindex (J' := J') (deriv k p) = deriv k (reindex (J' := J') p) := by
  induction p with
  | zero | smoothF _ | coeff _ _ _ | jet _ => rfl
  | add p q hp hq => simp [deriv, reindex, hp, hq]
  | sub p q hp hq => simp [deriv, reindex, hp, hq]
  | coeffMul i j w p hp => simp [deriv, reindex, hp]
  | potentialMul w p hp => simp [deriv, reindex, hp]
  | sum p ih =>
      simp only [deriv, reindex]
      congr 1
      funext i
      exact ih i

theorem reindex_commutator (w : List ι) (k : ι) :
    reindex (J' := J')
        (commutator (b := b) (J := J) (A := A) (F := F) w k) =
      commutator (b := b) (J := J') (A := A) (F := F) w k := by
  simp [commutator, reindex]

theorem reindex_forcing (w : List ι) :
    reindex (J' := J')
        (forcing (b := b) (J := J) (A := A) (F := F) w) =
      forcing (b := b) (J := J') (A := A) (F := F) w := by
  induction w with
  | nil => rfl
  | cons k w ih =>
      simp only [forcing]
      simp only [reindex]
      rw [reindex_deriv, reindex_commutator, ih]

theorem eval_forcing_restrict
    {ι : Type*} [Fintype ι] {b : ι → E} {S K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) (hSK : S ⊆ K)
    (A : E → ι → ι → ℝ) (F : E → ℝ) (w : List ι) :
    (forcing (b := b) (J := J.restrict hSK) (A := A) (F := F) w).eval =
      (forcing (b := b) (J := J) (A := A) (F := F) w).eval := by
  have hJ : ∀ v : List ι, J.value v = (J.restrict hSK).value v := by
    intro v
    exact (LocalL2DerivativeJet.restrict_value J hSK v).symm
  calc
    (forcing (b := b) (J := J.restrict hSK) (A := A) (F := F) w).eval =
        (reindex (J' := J.restrict hSK)
          (forcing (b := b) (J := J) (A := A) (F := F) w)).eval := by
      rw [reindex_forcing (J := J) (J' := J.restrict hSK)
        (A := A) (F := F) w]
    _ = (forcing (b := b) (J := J) (A := A) (F := F) w).eval := by
      exact (eval_reindex_eq_all
        (J := J) (J' := J.restrict hSK)
        (forcing (b := b) (J := J) (A := A) (F := F) w) hJ).symm

theorem eval_forcing_reindex_eq (w : List ι)
    (hJ : ∀ v : List ι, v.length ≤ n → J.value v = J'.value v)
    (hw : w.length + 1 ≤ n) :
    (forcing (b := b) (J := J) (A := A) (F := F) w).eval =
      (forcing (b := b) (J := J') (A := A) (F := F) w).eval := by
  rw [← reindex_forcing (J := J) (J' := J') (A := A) (F := F) w]
  apply eval_reindex_eq
  · exact hJ
  · exact (jetBound_forcing_le (b := b) (J := J) (A := A) (F := F) w).trans hw

theorem forcing_cons_eval
    {ι : Type*} [Fintype ι] {b : ι → E} {K : Set E} {n : ℕ}
    {J : LocalL2DerivativeJet b K n} {A : E → ι → ι → ℝ} {F : E → ℝ}
    (k : ι) (w : List ι) :
    (forcing (b := b) (J := J) (A := A) (F := F) (k :: w)).eval =
      (fun z => (deriv k
        (forcing (b := b) (J := J) (A := A) (F := F) w)).eval z -
        ∑ j, ∑ i,
          (fderiv ℝ (fun y => fderiv ℝ (fun x => A x i j) y (b k)) z (b j) *
              J.value (i :: w) z +
            fderiv ℝ (fun y => A y i j) z (b k) * J.value (j :: i :: w) z)) := by
  funext z
  simp [forcing, eval, deriv, commutator, localDirectionalIterate]

end ReactionExpr



def ReactionHierarchy
    {ι : Type*} [Fintype ι] {b : ι → E} {K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) (A : E → ι → ι → ℝ) (F : E → ℝ) : Prop :=
  ∀ w : List ι, w.length + 1 < n →
    weakCoefficientEquation A J w
      (ReactionExpr.forcing (b := b) (J := J) (A := A) (F := F) w).eval

theorem ReactionHierarchy.restrict
    {ι : Type*} [Fintype ι] {b : ι → E} {S K : Set E} {n : ℕ}
    {J : LocalL2DerivativeJet b K n} {A : E → ι → ι → ℝ} {F : E → ℝ}
    (h : ReactionHierarchy J A F) (hSK : S ⊆ K) :
    ReactionHierarchy (J.restrict hSK) A F := by
  intro w hw
  have h0 := weakCoefficientEquation.restrict (h w hw) hSK
  rw [ReactionExpr.eval_forcing_restrict J hSK A F w]
  exact h0


namespace ReactionExpr

variable {ι : Type uι} [Fintype ι]
  {K₁ K₂ : Set E} {n₁ n₂ : ℕ} {b : ι → E}
  {J₁ : LocalL2DerivativeJet b K₁ n₁}
  {J₂ : LocalL2DerivativeJet b K₂ n₂}
  {A : E → ι → ι → ℝ} {F : E → ℝ}

def reindexCross (p : ReactionExpr b J₁ A F) : ReactionExpr b J₂ A F :=
  match p with
  | .zero => .zero
  | .smoothF w => .smoothF w
  | .coeff i j w => .coeff i j w
  | .jet w => .jet w
  | .add p q => .add (reindexCross p) (reindexCross q)
  | .sub p q => .sub (reindexCross p) (reindexCross q)
  | .coeffMul i j w p => .coeffMul i j w (reindexCross p)
  | .potentialMul w p => .potentialMul w (reindexCross p)
  | .sum p => .sum (fun i => reindexCross (p i))

theorem eval_reindexCross_eq_of_bound
    (p : ReactionExpr b J₁ A F)
    {m : ℕ} (hJ : ∀ w : List ι, w.length ≤ m → J₁.value w = J₂.value w)
    (hp : p.jetBound ≤ m) :
    p.eval = (reindexCross (J₂ := J₂) p).eval := by
  induction p with
  | zero => rfl
  | smoothF _ => rfl
  | coeff _ _ _ => rfl
  | jet w =>
      have hw : w.length ≤ m := by simpa [jetBound] using hp
      simpa [eval, reindexCross] using congrArg
        (fun z : Lp ℝ 2 (volume : Measure E) => (z : E → ℝ)) (hJ w hw)
  | add p q ihp ihq =>
      have hp' : p.jetBound ≤ m := le_trans (le_max_left _ _) hp
      have hq' : q.jetBound ≤ m := le_trans (le_max_right _ _) hp
      funext z
      simp only [eval, reindexCross]
      rw [congrFun (ihp hp') z, congrFun (ihq hq') z]
  | sub p q ihp ihq =>
      have hp' : p.jetBound ≤ m := le_trans (le_max_left _ _) hp
      have hq' : q.jetBound ≤ m := le_trans (le_max_right _ _) hp
      funext z
      simp only [eval, reindexCross]
      rw [congrFun (ihp hp') z, congrFun (ihq hq') z]
  | coeffMul i j w p ih =>
      have hp' : p.jetBound ≤ m := by simpa [jetBound] using hp
      funext z
      simp only [eval, reindexCross]
      rw [congrFun (ih hp') z]
  | potentialMul w p ih =>
      have hp' : p.jetBound ≤ m := by simpa [jetBound] using hp
      funext z
      simp only [eval, reindexCross]
      rw [congrFun (ih hp') z]
  | sum p ih =>
      funext z
      simp only [eval, reindexCross]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : (p i).jetBound ≤ Finset.sup Finset.univ
          (fun j => (p j).jetBound) :=
        Finset.le_sup (s := Finset.univ) (f := fun j => (p j).jetBound)
          (b := i) (Finset.mem_univ i)
      exact congrFun (ih i (le_trans hi' hp)) z

theorem reindexCross_deriv (k : ι) (p : ReactionExpr b J₁ A F) :
    reindexCross (J₂ := J₂) (deriv k p) =
      deriv k (reindexCross (J₂ := J₂) p) := by
  induction p with
  | zero | smoothF _ | coeff _ _ _ | jet _ => rfl
  | add p q hp hq => simp [deriv, reindexCross, hp, hq]
  | sub p q hp hq => simp [deriv, reindexCross, hp, hq]
  | coeffMul i j w p hp => simp [deriv, reindexCross, hp]
  | potentialMul w p hp => simp [deriv, reindexCross, hp]
  | sum p ih =>
      simp only [deriv, reindexCross]
      congr 1
      funext i
      exact ih i

theorem reindexCross_commutator (w : List ι) (k : ι) :
    reindexCross (J₂ := J₂)
        (commutator (b := b) (J := J₁) (A := A) (F := F) w k) =
      commutator (b := b) (J := J₂) (A := A) (F := F) w k := by
  simp [commutator, reindexCross]

theorem reindexCross_forcing (w : List ι) :
    reindexCross (J₂ := J₂)
        (forcing (b := b) (J := J₁) (A := A) (F := F) w) =
      forcing (b := b) (J := J₂) (A := A) (F := F) w := by
  induction w with
  | nil => rfl
  | cons k w ih =>
      simp only [forcing]
      simp only [reindexCross]
      rw [reindexCross_deriv, reindexCross_commutator, ih]

theorem eval_forcing_cross_eq_of_bound
    (w : List ι)
    {m : ℕ} (hJ : ∀ v : List ι, v.length ≤ m → J₁.value v = J₂.value v)
    (hw : w.length + 1 ≤ m) :
    (forcing (b := b) (J := J₁) (A := A) (F := F) w).eval =
      (forcing (b := b) (J := J₂) (A := A) (F := F) w).eval := by
  calc
    (forcing (b := b) (J := J₁) (A := A) (F := F) w).eval =
        (reindexCross (J₂ := J₂)
          (forcing (b := b) (J := J₁) (A := A) (F := F) w)).eval :=
      eval_reindexCross_eq_of_bound _ hJ
        ((jetBound_forcing_le (b := b) (J := J₁) (A := A) (F := F) w).trans hw)
    _ = (forcing (b := b) (J := J₂) (A := A) (F := F) w).eval := by
      rw [reindexCross_forcing]

end ReactionExpr

/-! ## One elliptic bootstrap step -/

theorem exists_reaction_jet_successor
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) {K S W : Set E} {n : ℕ}
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (hS : IsCompact S) (hSK : S ⊆ interior K)
    (hW : IsOpen W) (hKW : K ⊆ W)
    (A : E → Matrix ι ι ℝ) (F : E → ℝ)
    (hA : ContDiffOn ℝ ∞ A W) (hF : ContDiffOn ℝ ∞ F W)
    {ell Lam : ℝ} (hell : 0 < ell) (hLam : 0 ≤ Lam)
    (hEll : ∀ x ∈ K, ∀ u : EuclideanSpace ℝ ι,
      ell * ‖u‖ ^ 2 ≤ ∑ i, ∑ j, A x i j * u i * u j)
    (hbil : ∀ x ∈ K, ∀ u w : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, A x i j * u i * w j| ≤ Lam * ‖u‖ * ‖w‖)
    (J : LocalL2DerivativeJet (fun i => b i) K n)
    (hJ : ReactionHierarchy J A F) (hn : 2 ≤ n) :
    ∃ J' : LocalL2DerivativeJet (fun i => b i) S (n + 1),
      ReactionHierarchy J' A F ∧
        ∀ w : List ι, w.length ≤ n → J'.value w = J.value w := by
  classical
  have hAij (i j : ι) : ContDiffOn ℝ ∞ (fun z => A z i j) W := by
    exact contDiffOn_pi.mp (contDiffOn_pi.mp hA i) j
  obtain ⟨Cq, hCq, hAq⟩ := exists_matrix_quotient_bound hK hW hKW hconv hA
  obtain ⟨T, hT, hST, hTK⟩ := exists_compact_between hS isOpen_interior hSK
  have hTKK : T ⊆ K := hTK.trans interior_subset
  have hTW : T ⊆ W := hTKK.trans hKW
  obtain ⟨η, Oη, εη, hη, hcη, hsη, hrη, hOη, hSη, hOηT, hηone, hεη,
      hmarginη⟩ := exists_smooth_compact_plateau hS isOpen_interior hST
  have hηC1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hηabs : ∀ x, |η x| ≤ 1 := by
    intro x
    rcases hrη x with ⟨hx0, hx1⟩
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨χ, Oχ, εχ, hχ, hcχ, hsχ, hrχ, hOχ, hηOχ, hOχT, hχone, hεχ,
      hmarginχ⟩ := exists_smooth_plateau_for_cutoff η hcη isOpen_interior hsη
  have hOχK : Oχ ⊆ K := hOχT.trans interior_subset |>.trans hTKK
  have hχT : tsupport χ ⊆ T := hsχ.trans interior_subset
  have hχintT : tsupport χ ⊆ interior T := hsχ
  obtain ⟨H, hH, hgrad⟩ := exists_cutoff_coordinate_gradient_bound b η hηC1 hcη

  have hnewEquation (k : ι) (w : List ι) (hw : w.length + 1 < n) :
      ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
        tsupport φ ⊆ T →
        (∑ j, ∫ z in T, (∑ i, A z i j * J.value (i :: k :: w) z) *
          fderiv ℝ φ z (b j)) =
          -(∫ z in T,
            (ReactionExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F)
              (k :: w)).eval z * φ z) := by
    intro φ hφ hcφ hsφ
    let p₀ := ReactionExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F) w
    have hp₀ : p₀.jetBound + 1 ≤ n := by
      have hbound := ReactionExpr.jetBound_forcing_le (b := fun i => b i)
        (J := J) (A := A) (F := F) w
      dsimp [p₀]
      omega
    have hwp₀ := ReactionExpr.weak_derivative_eval hK hW hKW hAij hF p₀ hp₀ k
    have hdF₀ : MemLp (ReactionExpr.deriv k p₀).eval 2 (volume.restrict K) := by
      apply ReactionExpr.memLp_eval hK hW hKW hAij hF
      exact (ReactionExpr.jetBound_deriv_le k p₀).trans hp₀
    obtain ⟨hGmem, hGeq⟩ := J.exists_scalar_forcing_differentiated_equation_of_weak_forcing
      w hw hK hW hKW k A p₀.eval (ReactionExpr.deriv k p₀).eval hAij hdF₀ hwp₀ (hJ w hw)
    let G : E → ℝ := fun z =>
      (ReactionExpr.deriv k p₀).eval z - ∑ j, ∑ i,
        (fderiv ℝ (fun y => fderiv ℝ (fun x => A x i j) y (b k)) z (b j) *
            J.value (i :: w) z +
          fderiv ℝ (fun y => A y i j) z (b k) * J.value (j :: i :: w) z)
    have hGmem' : MemLp G 2 (volume.restrict K) := by
      simpa [G] using hGmem
    have hGforcing : G =
        (ReactionExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F)
          (k :: w)).eval := by
      simpa [G, p₀] using
        (ReactionExpr.forcing_cons_eval (b := fun i => b i) (J := J) (A := A)
          (F := F) k w).symm
    let P : ι → E → ℝ := fun j z => ∑ i, A z i j * J.value (k :: i :: w) z
    have hP (j : ι) : MemLp (P j) 2 (volume.restrict K) := by
      apply memLp_finsetSum
      intro i hi
      exact memLp_mul_coefficient_on_compact hK
        ((hAij i j).continuousOn.mono hKW)
        ((Lp.memLp (J.value (k :: i :: w))).restrict K)
    have hPDE : ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ K →
        (∑ j, ∫ z in K, P j z * fderiv ℝ θ z (b j)) =
          -(∫ z in K, G z * θ z) := by
      intro θ hθ hcθ hsθ
      have hh := hGeq θ hθ hcθ hsθ
      simpa [P, G] using hh
    have hC1 := extend_weak_test_equation_to_c1 b hT hK hTK P G hP hGmem' hPDE
      φ hφ hcφ hsφ
    have hmix (i : ι) : J.value (k :: i :: w) =ᵐ[volume.restrict T]
        J.value (i :: k :: w) := by
      exact (J.mixed_adjacent_ae_eq_interior k i w (by omega)).filter_mono
        (ae_mono (Measure.restrict_mono_set volume hTK))
    have hflux (j : ι) :
        (∫ z in T, P j z * fderiv ℝ φ z (b j)) =
          ∫ z in T, (∑ i, A z i j * J.value (i :: k :: w) z) *
            fderiv ℝ φ z (b j) := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hmix] with z hz
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hz i]
    calc
      (∑ j, ∫ z in T, (∑ i, A z i j * J.value (i :: k :: w) z) *
          fderiv ℝ φ z (b j)) =
          ∑ j, ∫ z in T, P j z * fderiv ℝ φ z (b j) := by
        exact (Finset.sum_congr rfl (fun j _ => hflux j)).symm
      _ = -(∫ z in T, G z * φ z) := hC1
      _ = -(∫ z in T,
          (ReactionExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F)
            (k :: w)).eval z * φ z) := by rw [hGforcing]

  have htailEquation (w : List ι) (hw : w.length + 1 = n) :
      ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
        tsupport φ ⊆ T →
        (∑ j, ∫ z in T, (∑ i, A z i j * J.value (i :: w) z) *
          fderiv ℝ φ z (b j)) =
          -(∫ z in T,
            (ReactionExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F)
              w).eval z * φ z) := by
    intro φ hφ hcφ hsφ
    have hne : w ≠ [] := by
      intro hzero
      subst w
      simp at hw
      omega
    obtain ⟨k, w₀, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact hnewEquation k w₀ (by
      simp only [List.length_cons] at hw
      omega) φ hφ hcφ hsφ

  have hnew : ∀ w : List ι, w.length = n → ∀ k : ι, ∃ g : Lp ℝ 2 (volume : Measure E),
      HasWeakDirectionalDerivativeOn S (b k) (J.value w) g := by
    intro w hw k
    have hwne : w ≠ [] := by
      intro hzero
      subst w
      simp at hw
      omega
    obtain ⟨i, tail, rfl⟩ := List.exists_cons_of_ne_nil hwne
    have htail : tail.length + 1 = n := by
      simp only [List.length_cons] at hw
      omega
    have htail_lt : tail.length < n := by omega
    let Jtail := shiftedLocalJet J hTKK tail htail_lt
    let p : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E)) :=
      ((localizedWeakJet_properties Jtail hχ hcχ []).1.toLp
          (localizedWeakJet Jtail χ []),
        fun j => (localizedWeakJet_properties Jtail hχ hcχ [j]).1.toLp
          (localizedWeakJet Jtail χ [j]))
    have hp : p ∈ closure (c1SupportedTestGraph (fun j => b j) T) := by
      dsimp [p]
      exact localizedWeakJet_mem_c1SupportedTestGraph_of_weak Jtail hχ hcχ
        hχT hT hχintT (by simp)
    have hpD (j : ι) : ∀ᵐ x ∂(volume : Measure E), x ∈ Oχ →
        p.2 j x = J.value (j :: tail) x := by
      have hae := (localizedWeakJet_properties Jtail hχ hcχ [j]).1.coeFn_toLp
      filter_upwards [hae] with x hx
      intro hxO
      have hloc : localizedWeakJet Jtail χ [j] x = J.value (j :: tail) x := by
        simp [localizedWeakJet, cutoffJetTerms, cutoffJetTerm, localDirectionalIterate,
          Jtail, shiftedLocalJet, hχone hxO,
          fderiv_eq_zero_on_plateau hOχ hχone hxO, List.map_append, List.sum_append]
      exact hx.trans hloc
    have hU : MemLp (J.value tail) 2 (volume.restrict T) :=
      (Lp.memLp (J.value tail)).restrict T
    have hD (j : ι) : MemLp (J.value (j :: tail)) 2 (volume.restrict T) :=
      (Lp.memLp (J.value (j :: tail))).restrict T
    have hFtail : MemLp
        (ReactionExpr.forcing (b := fun j => b j) (J := J) (A := A) (F := F) tail).eval
        2 (volume.restrict T) := by
      have hjet : (ReactionExpr.forcing (b := fun j => b j) (J := J)
          (A := A) (F := F) tail).jetBound ≤ n := by
        exact (ReactionExpr.jetBound_forcing_le (b := fun j => b j)
          (J := J) (A := A) (F := F) tail).trans (by omega)
      have hFtailK : MemLp
          (ReactionExpr.forcing (b := fun j => b j) (J := J) (A := A) (F := F) tail).eval
          2 (volume.restrict K) := by
        exact ReactionExpr.memLp_eval (J := J) (A := fun z i j => A z i j) (F := F)
          hK hW hKW hAij hF
          (ReactionExpr.forcing (b := fun j => b j) (J := J) (A := A) (F := F) tail)
          hjet
      simpa only [MeasureTheory.Measure.restrict_restrict_of_subset hTKK] using
        hFtailK.restrict T
    have hweakTail : ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
        tsupport φ ⊆ T → ∀ j,
        (∫ z in T, J.value tail z * fderiv ℝ φ z (b j)) =
          -(∫ z in T, J.value (j :: tail) z * φ z) := by
      intro φ hφ hcφ hsφ j
      have hext := extend_weak_directional_derivative_to_c1 b j hT hK hTK
        (J.value tail) (J.value (j :: tail))
        ((Lp.memLp (J.value tail)).restrict K)
        ((Lp.memLp (J.value (j :: tail))).restrict K) (by
          intro θ hθ hcθ hsθ
          exact J.weak tail (by omega) j θ hθ hcθ hsθ)
      exact hext φ hφ hcφ hsφ
    let d : LocalWeakPoissonData b T A (J.value tail)
        (ReactionExpr.forcing (b := fun j => b j) (J := J) (A := A) (F := F) tail).eval
        (fun j => J.value (j :: tail)) :=
      { solution_memLp := hU
        forcing_memLp := hFtail
        derivative_memLp := hD
        weakDerivative := hweakTail
        variational := by
          letI : IsFiniteMeasure (volume.restrict T) :=
            isFiniteMeasure_restrict.mpr hT.measure_lt_top.ne
          intro θ hθ hcθ hsθ
          have hh := htailEquation tail htail θ hθ hcθ hsθ
          have hflux (j : ι) : Integrable
              (fun z => (∑ i, A z i j * J.value (i :: tail) z) *
                fderiv ℝ θ z (b j)) (volume.restrict T) := by
            have hAj : MemLp (fun z => ∑ i, A z i j * J.value (i :: tail) z)
                2 (volume.restrict T) := by
              apply memLp_finsetSum
              intro q hq
              exact memLp_mul_coefficient_on_compact hT
                ((hAij q j).continuousOn.mono hTW)
                ((Lp.memLp (J.value (q :: tail))).restrict T)
            have hθj : MemLp (fun z => fderiv ℝ θ z (b j))
                  2 (volume.restrict T) :=
                (((hθ.continuous_fderiv (by norm_num)).clm_apply
                  (continuous_const (y := b j))).memLp_of_hasCompactSupport
                  (hcθ.fderiv_apply ℝ (b j))).restrict T
            exact hAj.integrable_mul hθj
          have hsum : (fun z => ∑ i, ∑ j,
                A z i j * J.value (i :: tail) z * fderiv ℝ θ z (b j)) =
                (fun z => ∑ j, (∑ i, A z i j * J.value (i :: tail) z) *
                  fderiv ℝ θ z (b j)) := by
            funext z
            simp_rw [Finset.sum_mul]
            exact Finset.sum_comm
          calc
            (∫ z in T, ∑ i, ∑ j,
                A z i j * J.value (i :: tail) z * fderiv ℝ θ z (b j)) =
                ∫ z in T, ∑ j, (∑ i, A z i j * J.value (i :: tail) z) *
                  fderiv ℝ θ z (b j) := by rw [hsum]
            _ = ∑ j, ∫ z in T, (∑ i, A z i j * J.value (i :: tail) z) *
                  fderiv ℝ θ z (b j) := by
              rw [integral_finsetSum]
              intro j hj
              exact hflux j
            _ = -(∫ z in T,
                (ReactionExpr.forcing (b := fun j => b j) (J := J) (A := A)
                  (F := F) tail).eval z * θ z) := hh }
    obtain ⟨L, hL, hLq⟩ := exists_cutoff_differenceQuotient_bound η hηC1 hcη
    let Gp : ℝ := Real.sqrt (∑ j, ‖p.2 j‖ ^ 2)
    let Rv : ℝ := ‖b k‖ * Gp
    let Lq : ℝ := (Fintype.card ι : ℝ) ^ 2 * Cq
    let Zq : ℝ := ‖d.globalForcing hT.measurableSet‖ * ‖b k‖
    let Ctail : ℝ := Real.sqrt ((2 * Lam * H * Rv + Lq * Gp + Zq) ^ 2 +
      2 * ell * (2 * Lq * H * Gp * Rv + 2 * H * Zq * Rv)) / ell
    have hbound : ∀ h : ℝ, h ≠ 0 → |h| < εχ →
        ∃ r : Lp (EuclideanSpace ℝ ι) 2 (volume : Measure E),
          (∀ᵐ x ∂(volume : Measure E),
            r x i = η x * directionalDifferenceQuotient (J.value (i :: tail)) (b k) h x) ∧
          ‖r‖ ≤ Ctail := by
      intro h hh hsmall
      have hsmall' : |h| * ‖b k‖ < εχ := by simpa [b.norm_eq_one] using hsmall
      obtain ⟨hends, hpreplus, hpreminus⟩ := hmarginχ (b k) h hsmall'
      have hshift : ∀ x ∈ tsupport η, x + h • b k ∈ Oχ := by
        intro x hx
        exact (hends x (Or.inl hx)).1
      have hback : (fun x => x + (-h) • b k) ⁻¹' tsupport η ⊆ T := by
        exact hpreminus.trans (hOχT.trans interior_subset)
      have hquot : ∀ x ∈ tsupport η,
          ‖h⁻¹ • (A (x + h • b k) - A x)‖ ≤ Cq := by
        intro x hx
        have hxT : x ∈ T := interior_subset (hsη hx)
        have hxK : x ∈ K := hTKK hxT
        have hxhO := hshift x hx
        have hxhK : x + h • b k ∈ K := hOχK (hxhO)
        simpa using hAq x (b k) h hh hxK hxhK
      have hdη := hgrad
      obtain ⟨r, hr, hrnorm⟩ := d.exists_local_weighted_derivative_quotient_bound
        hT (hA.continuousOn.mono hTW) p hp hpD η hηC1 hcη hηabs hηOχ
        (hOχT.trans interior_subset)
        (b k) h hh hshift hback hell hLam hCq hH
        (fun x hx u => hEll x (hTKK hx) u)
        (fun x hx u w => hbil x (hTKK hx) u w) hquot hdη
      refine ⟨r, ?_, ?_⟩
      · filter_upwards [hr, directionalDifferenceQuotient_ae_eq
          (J.value (i :: tail)) (b k) h] with x hx hq
        exact (hx i).trans (by rw [hq])
      · simpa [Gp, Rv, Lq, Zq, Ctail] using hrnorm
    have hηb : ∀ᵐ x ∂(volume : Measure E), ‖η x‖ ≤ 1 := by
      exact Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hηabs x)
    have hηS : ∀ x ∈ S, η x = 1 := fun x hx => hηone (hSη hx)
    have hLqk : ∀ (x : E) (h : ℝ), h ≠ 0 →
        ‖h⁻¹ * (η (x + h • b k) - η x)‖ ≤ L := by
      intro x h hh
      simpa [b.norm_eq_one] using hLq x (b k) h hh
    obtain ⟨g, hg, hweak⟩ := exists_local_weak_derivative_of_weighted_quotient_bound
      hS (J.value (i :: tail)) (b k) hηC1 hcη hηb hηS L hL hLqk Ctail εχ hεχ i hbound
    exact ⟨g, hweak⟩
  have hSKK : S ⊆ K := hSK.trans interior_subset
  let JS : LocalL2DerivativeJet (fun i => b i) S n := J.restrict hSKK
  obtain ⟨J', hpres⟩ := JS.gain_of_local_weak_derivatives (by
    intro w hw k
    obtain ⟨g, hg⟩ := hnew w hw k
    exact ⟨g, by simpa [JS, LocalL2DerivativeJet.restrict] using hg⟩)
  have hJtoJ' (v : List ι) (hv : v.length ≤ n) :
      J.value v = J'.value v := by
    calc
      J.value v = JS.value v := by rfl
      _ = J'.value v := (hpres v hv).symm
  have htransport (w : List ι) (G : E → ℝ)
      (J₀ : LocalL2DerivativeJet (fun i => b i) S n)
      (h₀ : weakCoefficientEquation A J₀ w G)
      (hvalue : ∀ i : ι, J₀.value (i :: w) = J'.value (i :: w))
      (hforcing : G =
        (ReactionExpr.forcing (b := fun i => b i) (J := J') (A := A) (F := F) w).eval) :
      weakCoefficientEquation A J' w
        (ReactionExpr.forcing (b := fun i => b i) (J := J') (A := A) (F := F) w).eval := by
    intro φ hφ hcφ hsφ
    have hh := h₀ φ hφ hcφ hsφ
    calc
      (∑ j, ∫ z in S, (∑ i, A z i j * J'.value (i :: w) z) *
          fderiv ℝ φ z (b j)) =
          ∑ j, ∫ z in S, (∑ i, A z i j * J₀.value (i :: w) z) *
            fderiv ℝ φ z (b j) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply integral_congr_ae
        filter_upwards [] with z
        have hvalue' (i : ι) :
            (J'.value (i :: w) : E → ℝ) = (J₀.value (i :: w) : E → ℝ) :=
          congrArg (fun q : Lp ℝ 2 (volume : Measure E) => (q : E → ℝ))
            (hvalue i).symm
        simp_rw [hvalue']
      _ = -(∫ z in S, G z * φ z) := hh
      _ = -(∫ z in S,
          (ReactionExpr.forcing (b := fun i => b i) (J := J') (A := A) (F := F) w).eval z * φ z) := by
        rw [hforcing]
  refine ⟨J', ?_, ?_⟩
  intro w hw
  have hwle : w.length + 1 ≤ n := by omega
  by_cases hlow : w.length + 1 < n
  · have hbase := weakCoefficientEquation.restrict (hJ w hlow) hSKK
    have h₀ : weakCoefficientEquation A JS w
        (ReactionExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F) w).eval := by
      simpa [JS] using hbase
    have hforcing := ReactionExpr.eval_forcing_cross_eq_of_bound
      (J₁ := J) (J₂ := J') (A := fun z i j => A z i j) (F := F) w
      hJtoJ' hwle
    apply htransport w
      (ReactionExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F) w).eval
      JS h₀
    · intro i
      exact (hpres (i :: w) (by simp only [List.length_cons]; omega)).symm
    · exact hforcing
  · have hwEq : w.length + 1 = n := by omega
    have hSTT : S ⊆ T := hST.trans interior_subset
    let JT : LocalL2DerivativeJet (fun i => b i) T n := J.restrict hTKK
    have hT₀ : weakCoefficientEquation A JT w
        (ReactionExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F) w).eval := by
      intro θ hθ hcθ hsθ
      exact htailEquation w hwEq θ (hθ.of_le (by norm_num)) hcθ hsθ
    have hS₀ := weakCoefficientEquation.restrict hT₀ hSTT
    let JTS : LocalL2DerivativeJet (fun i => b i) S n := JT.restrict hSTT
    have h₀ : weakCoefficientEquation A JTS w
        (ReactionExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F) w).eval := by
      simpa [JTS] using hS₀
    have hforcing := ReactionExpr.eval_forcing_cross_eq_of_bound
      (J₁ := J) (J₂ := J') (A := fun z i j => A z i j) (F := F) w
      hJtoJ' hwle
    apply htransport w
      (ReactionExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F) w).eval
      JTS h₀
    · intro i
      calc
        JTS.value (i :: w) = J.value (i :: w) := by rfl
        _ = J'.value (i :: w) := hJtoJ' _ (by simp only [List.length_cons]; omega)
    · exact hforcing
  intro v hv
  exact (hJtoJ' v hv).symm

/-! ## Iteration over nested compact sets -/

def LocalL2DerivativeJet.truncate
    {ι : Type*} {b : ι → E} {K : Set E} {k l : ℕ}
    (J : LocalL2DerivativeJet b K k) (hlk : l ≤ k) :
    LocalL2DerivativeJet b K l :=
  ⟨J.value, fun w hw i => J.weak w (by omega) i⟩

/-- Starting with an order-two jet and its zeroth-level coefficient equation,
successive compact interiors carry jets of every order.  The compact sequence
is the bookkeeping device that supplies a fresh interior margin at each
successor; no derivative-quotient estimate is assumed in this theorem. -/
theorem exists_reaction_jets_on_nested_compacts
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) {K : ℕ → Set E} {S W : Set E}
    (hK : ∀ m, IsCompact (K m)) (hconv : ∀ m, Convex ℝ (K m))
    (hstep : ∀ m, K (m + 1) ⊆ interior (K m))
    (hS : IsCompact S) (hSall : ∀ m, S ⊆ interior (K m))
    (hW : IsOpen W) (hKW : K 0 ⊆ W)
    (A : E → Matrix ι ι ℝ) (F : E → ℝ)
    (hA : ContDiffOn ℝ ∞ A W) (hF : ContDiffOn ℝ ∞ F W)
    {ell Lam : ℝ} (hell : 0 < ell) (hLam : 0 ≤ Lam)
    (hEll : ∀ x ∈ K 0, ∀ u : EuclideanSpace ℝ ι,
      ell * ‖u‖ ^ 2 ≤ ∑ i, ∑ j, A x i j * u i * u j)
    (hbil : ∀ x ∈ K 0, ∀ u w : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, A x i j * u i * w j| ≤ Lam * ‖u‖ * ‖w‖)
    (J₂ : LocalL2DerivativeJet (fun i => b i) (K 0) 2)
    (hJ₂ : ReactionHierarchy J₂ A F) :
    ∀ n : ℕ, ∃ J : LocalL2DerivativeJet (fun i => b i) S n,
      ReactionHierarchy J A F ∧
        ∀ w : List ι, w.length ≤ 2 → J.value w = J₂.value w := by
  have hKsub0 : ∀ m, K m ⊆ K 0 := by
    intro m
    induction m with
    | zero => exact subset_rfl
    | succ m ih =>
        exact (hstep m).trans (interior_subset.trans ih)
  have hchain : ∀ m, ∃ Jm : LocalL2DerivativeJet (fun i => b i) (K m) (m + 2),
      ReactionHierarchy Jm A F ∧
        ∀ w : List ι, w.length ≤ 2 → Jm.value w = J₂.value w := by
    intro m
    induction m with
    | zero => exact ⟨J₂, hJ₂, fun w hw => rfl⟩
    | succ m ih =>
        obtain ⟨Jm, hJm, hbase⟩ := ih
        have hKWm : K m ⊆ W := (hKsub0 m).trans hKW
        have hEllm : ∀ x ∈ K m, ∀ u : EuclideanSpace ℝ ι,
            ell * ‖u‖ ^ 2 ≤ ∑ i, ∑ j, A x i j * u i * u j := by
          intro x hx u
          exact hEll x (hKsub0 m hx) u
        have hBilm : ∀ x ∈ K m, ∀ u w : EuclideanSpace ℝ ι,
            |∑ i, ∑ j, A x i j * u i * w j| ≤ Lam * ‖u‖ * ‖w‖ := by
          intro x hx u w
          exact hbil x (hKsub0 m hx) u w
        obtain ⟨Jnext, hJnext, hnext⟩ := exists_reaction_jet_successor b
          (K := K m) (S := K (m + 1)) (W := W) (n := m + 2)
          (hK m) (hconv m) (hK (m + 1)) (hstep m)
          hW hKWm A F hA hF hell hLam hEllm hBilm Jm hJm (by omega)
        exact ⟨Jnext, hJnext, fun w hw => (hnext w (by omega)).trans (hbase w hw)⟩
  intro n
  have hS0 : S ⊆ K 0 := (hSall 0).trans interior_subset
  by_cases hn : 2 ≤ n
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 2 = n := by
      exact ⟨n - 2, by omega⟩
    obtain ⟨Jm, hJm, hbase⟩ := hchain m
    have hSm : S ⊆ K m := (hSall m).trans interior_subset
    let Jn : LocalL2DerivativeJet (fun i => b i) S (m + 2) := Jm.restrict hSm
    have hJn : ReactionHierarchy Jn A F := hJm.restrict hSm
    subst n
    exact ⟨Jn, hJn, fun w hw => hbase w hw⟩
  · let Jsmall : LocalL2DerivativeJet (fun i => b i) S n :=
      (J₂.restrict hS0).truncate (by omega)
    refine ⟨Jsmall, ?_, ?_⟩
    unfold ReactionHierarchy
    intro w hw
    omega
    intro w hw
    rfl

/-! A base equation is exactly the order-two instance of the hierarchy. -/

theorem reactionHierarchy_of_order_two_equation
    {ι : Type uι} [Fintype ι]
    {b : ι → E} {K : Set E}
    {A : E → Matrix ι ι ℝ} {F : E → ℝ}
    (J : LocalL2DerivativeJet b K 2)
    (hbase : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (∑ i, A z i j * J.value (i :: []) z) *
        fderiv ℝ φ z (b j)) = -(∫ z in K, (F z * J.value [] z) * φ z)) :
    ReactionHierarchy J A F := by
  intro w hw
  have hw0 : w.length = 0 := by omega
  have hw_nil : w = [] := List.eq_nil_of_length_eq_zero hw0
  subst w
  simpa [weakCoefficientEquation, ReactionExpr.forcing, ReactionExpr.eval,
    localDirectionalIterate] using hbase


end LichnerowiczObata.Reaction
