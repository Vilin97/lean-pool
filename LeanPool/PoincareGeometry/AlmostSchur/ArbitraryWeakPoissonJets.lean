/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.WeakPoissonAllOrderJets
public import LeanPool.PoincareGeometry.AlmostSchur.WeakH1GraphClosure
public import LeanPool.PoincareGeometry.AlmostSchur.ScalarCommutatorForcing
public import LeanPool.PoincareGeometry.AlmostSchur.DifferenceQuotientProduct
public import LeanPool.PoincareGeometry.AlmostSchur.CutoffPlateau
public import LeanPool.PoincareGeometry.AlmostSchur.LocalH2QuotientBound
public import LeanPool.PoincareGeometry.AlmostSchur.LocalizedDerivativeExtraction
public import LeanPool.PoincareGeometry.AlmostSchur.WeakPoissonH2Bound
public import LeanPool.PoincareGeometry.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Approximation
public import LeanPool.PoincareGeometry.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Kernels
public import LeanPool.PoincareGeometry.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.TranslationIntegral
public import LeanPool.PoincareGeometry.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# The finite-order elliptic bootstrap

This file supplies the missing analytic mechanism behind the finite-order
Poisson regularity endpoint.  The forcing created by differentiating a
divergence equation is represented as a small differential algebra of smooth
coefficient expressions and weak jet fields.  This keeps the forcing's weak
derivatives explicit, so that the difference-quotient estimate can be iterated
without assuming any quotient bounds.

The geometric assembly is deliberately left to a later file.  In particular,
all statements here are local Euclidean statements with the actual graph and
quotient estimates as inputs.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators

namespace AlmostSchur
universe uE uι

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## A weak differential expression language -/

inductive WeakExpr {ι : Type uι} {K : Set E} {n : ℕ}
    (b : ι → E) (J : LocalL2DerivativeJet b K n)
    (A : E → ι → ι → ℝ) (F : E → ℝ) : Type (max uE uι)
  | zero
  | smoothF (w : List ι)
  | coeff (i j : ι) (w : List ι)
  | jet (w : List ι)
  | add (p q : WeakExpr b J A F)
  | sub (p q : WeakExpr b J A F)
  | coeffMul (i j : ι) (w : List ι) (p : WeakExpr b J A F)
  | sum (p : ι → WeakExpr b J A F)

namespace WeakExpr

variable {ι : Type uι} [Fintype ι] {K : Set E} {n : ℕ}
  {b : ι → E} {J : LocalL2DerivativeJet b K n}
  {A : E → ι → ι → ℝ} {F : E → ℝ}

def eval : WeakExpr b J A F → E → ℝ
  | .zero => fun _ => 0
  | .smoothF w => localDirectionalIterate b F w
  | .coeff i j w => localDirectionalIterate b (fun z => A z i j) w
  | .jet w => fun z => J.value w z
  | .add p q => fun z => eval p z + eval q z
  | .sub p q => fun z => eval p z - eval q z
  | .coeffMul i j w p => fun z =>
      localDirectionalIterate b (fun y => A y i j) w z * eval p z
  | .sum p => fun z => ∑ i, eval (p i) z

def jetBound : WeakExpr b J A F → ℕ
  | .zero => 0
  | .smoothF _ => 0
  | .coeff _ _ _ => 0
  | .jet w => w.length
  | .add p q => max (jetBound p) (jetBound q)
  | .sub p q => max (jetBound p) (jetBound q)
  | .coeffMul _ _ _ p => jetBound p
  | .sum p => Finset.sup Finset.univ (fun i => jetBound (p i))

def deriv (k : ι) : WeakExpr b J A F → WeakExpr b J A F
  | .zero => .zero
  | .smoothF w => .smoothF (k :: w)
  | .coeff i j w => .coeff i j (k :: w)
  | .jet w => .jet (k :: w)
  | .add p q => .add (deriv k p) (deriv k q)
  | .sub p q => .sub (deriv k p) (deriv k q)
  | .coeffMul i j w p =>
      .add (.coeffMul i j (k :: w) p) (.coeffMul i j w (deriv k p))
  | .sum p => .sum (fun i => deriv k (p i))

def commutator (w : List ι) (k : ι) : WeakExpr b J A F :=
  .sum (fun j => .sum (fun i =>
    .add (.coeffMul i j [j, k] (.jet (i :: w)))
      (.coeffMul i j [k] (.jet (j :: i :: w)))))

def forcing : List ι → WeakExpr b J A F
  | [] => .smoothF []
  | k :: w => .sub (deriv k (forcing w)) (commutator w k)

private theorem jetBound_sum_le (p : ι → WeakExpr b J A F) (i : ι) :
    jetBound (p i) ≤ jetBound (.sum p) := by
  change jetBound (p i) ≤ Finset.sup Finset.univ (fun j => jetBound (p j))
  exact Finset.le_sup (s := Finset.univ) (f := fun j => jetBound (p j))
    (b := i) (Finset.mem_univ i)

theorem jetBound_deriv_le (k : ι) (p : WeakExpr b J A F) :
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

end WeakExpr

/-! ## Restricting the transposed coefficient equation -/

/-- The transposed coefficient equation attached to a weak derivative jet. -/
def weakCoefficientEquation
    {ι : Type*} [Fintype ι] {b : ι → E} {K : Set E} {n : ℕ}
    (A : E → ι → ι → ℝ) (J : LocalL2DerivativeJet b K n)
    (w : List ι) (G : E → ℝ) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
    (∑ j, ∫ z in K, (∑ i, A z i j * J.value (i :: w) z) *
      fderiv ℝ φ z (b j)) = -(∫ z in K, G z * φ z)

/-- The same transposed equation with an arbitrary flux field. -/
def weakDivergenceEquation
    {ι : Type*} [Fintype ι] {b : ι → E} {K : Set E}
    (A : E → ι → ι → ℝ) (D : ι → E → ℝ) (G : E → ℝ) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
    (∑ j, ∫ z in K, (∑ i, A z i j * D i z) *
      fderiv ℝ φ z (b j)) = -(∫ z in K, G z * φ z)

theorem weakDivergenceEquation.restrict
    {ι : Type*} [Fintype ι] {b : ι → E} {S K : Set E}
    {A : E → ι → ι → ℝ} {D : ι → E → ℝ} {G : E → ℝ}
    (h : weakDivergenceEquation (b := b) A D G (K := K)) (hSK : S ⊆ K) :
    weakDivergenceEquation (b := b) A D G (K := S) := by
  intro φ hφ hc hs
  have hzeroL (j : ι) (z : E) (hz : z ∉ S) :
      (∑ i, A z i j * D i z) * fderiv ℝ φ z (b j) = 0 := by
    simp [fderiv_of_notMem_tsupport ℝ (fun hh => hz (hs hh))]
  have hzeroR (z : E) (hz : z ∉ S) : G z * φ z = 0 := by
    simp [image_eq_zero_of_notMem_tsupport (fun hh => hz (hs hh))]
  have hzeroLK (j : ι) (z : E) (hz : z ∉ K) :
      (∑ i, A z i j * D i z) * fderiv ℝ φ z (b j) = 0 :=
    hzeroL j z (fun hzs => hz (hSK hzs))
  have hzeroRK (z : E) (hz : z ∉ K) : G z * φ z = 0 :=
    hzeroR z (fun hzs => hz (hSK hzs))
  calc
    (∑ j, ∫ z in S, (∑ i, A z i j * D i z) * fderiv ℝ φ z (b j)) =
        ∑ j, ∫ z in K, (∑ i, A z i j * D i z) * fderiv ℝ φ z (b j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hs_eq := setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := (volume : Measure E)) (s := S) (hzeroL j)
      have hk_eq := setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := (volume : Measure E)) (s := K) (hzeroLK j)
      exact hs_eq.trans hk_eq.symm
    _ = -(∫ z in K, G z * φ z) := h φ hφ hc (hs.trans hSK)
    _ = -(∫ z in S, G z * φ z) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroRK,
        setIntegral_eq_integral_of_forall_compl_eq_zero hzeroR]

/-! ## Commutation of adjacent weak directions -/

theorem LocalL2DerivativeJet.mixed_adjacent_ae_eq_interior
    {ι : Type*} {b : ι → E} {K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) (i k : ι) (w : List ι)
    (hw : w.length + 2 ≤ n) :
    (J.value (i :: k :: w) : E → ℝ) =ᵐ[volume.restrict (interior K)]
      J.value (k :: i :: w) := by
  let g : E → ℝ := fun z => J.value (i :: k :: w) z - J.value (k :: i :: w) z
  have hg : LocallyIntegrable g volume :=
    ((Lp.memLp (J.value (i :: k :: w))).sub
      (Lp.memLp (J.value (k :: i :: w)))).locallyIntegrable (by norm_num)
  have he := isOpen_interior.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hg.locallyIntegrableOn (interior K)) (fun φ hφ hc hs => ?_)
  · apply (ae_restrict_iff' isOpen_interior.measurableSet).mpr
    filter_upwards [he] with z hz
    intro hzk
    exact sub_eq_zero.mp (hz hzk)
  · have ht : MemLp φ 2 (volume : Measure E) :=
      hφ.continuous.memLp_of_hasCompactSupport hc
    have hzero (T : Set E) (hT : tsupport φ ⊆ T) (u : E → ℝ) :
        (∫ z in T, u z * φ z) = ∫ z, u z * φ z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hz (hT hh)), mul_zero])
    have hzero' (T : Set E) (ψ : E → ℝ) (hT : tsupport ψ ⊆ T) (u : E → ℝ) :
        (∫ z in T, u z * ψ z) = ∫ z, u z * ψ z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hz (hT hh)), mul_zero])
    have h1 := J.weak (k :: w) (by simp only [List.length_cons]; omega) i φ hφ hc
      (hs.trans interior_subset)
    have h2 := J.weak (i :: w) (by simp only [List.length_cons]; omega) k φ hφ hc
      (hs.trans interior_subset)
    have h3 := J.weak w (by omega) k
      (fun z => fderiv ℝ φ z (b i))
      (contDiff_smooth_test_derivative hφ (b i))
      (hc.fderiv_apply ℝ (b i))
      ((tsupport_fderiv_apply_subset ℝ (b i)).trans (hs.trans interior_subset))
    have h4 := J.weak w (by omega) i
      (fun z => fderiv ℝ φ z (b k))
      (contDiff_smooth_test_derivative hφ (b k))
      (hc.fderiv_apply ℝ (b k))
      ((tsupport_fderiv_apply_subset ℝ (b k)).trans (hs.trans interior_subset))
    simp_rw [smooth_test_derivatives_commute hφ _ (b i) (b k)] at h3
    have hti : tsupport (fun z => fderiv ℝ φ z (b i)) ⊆ K :=
      (tsupport_fderiv_apply_subset ℝ (b i)).trans (hs.trans interior_subset)
    have htk : tsupport (fun z => fderiv ℝ φ z (b k)) ⊆ K :=
      (tsupport_fderiv_apply_subset ℝ (b k)).trans (hs.trans interior_subset)
    have htik : tsupport (fun z => fderiv ℝ (fun y => fderiv ℝ φ y (b i)) z (b k)) ⊆ K :=
      (tsupport_fderiv_apply_subset ℝ (b k)).trans hti
    have htki : tsupport (fun z => fderiv ℝ (fun y => fderiv ℝ φ y (b k)) z (b i)) ⊆ K :=
      (tsupport_fderiv_apply_subset ℝ (b i)).trans htk
    rw [hzero' K (fun z => fderiv ℝ φ z (b i)) hti] at h1
    rw [hzero K (hs.trans interior_subset)] at h1
    rw [hzero' K (fun z => fderiv ℝ φ z (b k)) htk] at h2
    rw [hzero K (hs.trans interior_subset)] at h2
    rw [hzero' K (fun z => fderiv ℝ (fun y => fderiv ℝ φ y (b k)) z (b i)) htki] at h3
    rw [hzero' K (fun z => fderiv ℝ φ z (b i)) hti] at h3
    rw [hzero' K (fun z => fderiv ℝ (fun y => fderiv ℝ φ y (b k)) z (b i)) htki] at h4
    rw [hzero' K (fun z => fderiv ℝ φ z (b k)) htk] at h4
    change (∫ z, φ z * g z) = 0
    simp_rw [g, mul_sub, mul_comm (φ _)]
    have htop : (∫ z, J.value (i :: k :: w) z * φ z) =
        ∫ z, J.value (k :: i :: w) z * φ z := by
      linarith
    rw [integral_sub
      (f := fun z => J.value (i :: k :: w) z * φ z)
      (g := fun z => J.value (k :: i :: w) z * φ z)
      ((Lp.memLp _).integrable_mul ht) ((Lp.memLp _).integrable_mul ht)]
    exact sub_eq_zero.mpr htop

/-! ## A fully general differentiated coefficient equation -/

theorem exists_scalar_forcing_differentiated_equation_of_weak_family
    {ι : Type*} [Fintype ι] {b : ι → E} {K W : Set E}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (k : ι) (A : E → ι → ι → ℝ)
    (D : ι → E → ℝ) (dD : ι → ι → E → ℝ) (F dF : E → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) W)
    (hD : ∀ i, MemLp (D i) 2 (volume.restrict K))
    (hdD : ∀ l i, MemLp (dD l i) 2 (volume.restrict K))
    (hweak : ∀ l i, HasWeakDirectionalDerivativeOn K (b l) (D i) (dD l i))
    (hF : HasWeakDirectionalDerivativeOn K (b k) F dF)
    (hdF : MemLp dF 2 (volume.restrict K))
    (hPDE : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (∑ i, A z i j * D i z) *
        fderiv ℝ φ z (b j)) = -(∫ z in K, F z * φ z)) :
    MemLp (fun z => dF z - ∑ j, ∑ i,
      (fderiv ℝ (fun y => fderiv ℝ (fun x => A x i j) y (b k)) z (b j) * D i z +
        fderiv ℝ (fun y => A y i j) z (b k) * dD j i z)) 2
      (volume.restrict K) ∧
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (∑ i, A z i j * dD k i z) *
        fderiv ℝ φ z (b j)) = -(∫ z in K, (dF z - ∑ j, ∑ i,
          (fderiv ℝ (fun y => fderiv ℝ (fun x => A x i j) y (b k)) z (b j) * D i z +
            fderiv ℝ (fun y => A y i j) z (b k) * dD j i z)) * φ z) := by
  let P := fun j z => ∑ i, A z i j * dD k i z
  let C := fun j z => ∑ i, fderiv ℝ (fun y => A y i j) z (b k) * D i z
  let dC := fun j z => ∑ i,
    (fderiv ℝ (fun y => fderiv ℝ (fun x => A x i j) y (b k)) z (b j) * D i z +
      fderiv ℝ (fun y => A y i j) z (b k) * dD j i z)
  have hDA (i j : ι) : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ (fun y => A y i j) z (b k)) W :=
    ((hA i j).fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const
  have hD2 (i j : ι) : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ (fun y => fderiv ℝ (fun x => A x i j) y (b k)) z (b j)) W :=
    ((hDA i j).fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const
  have hC (j : ι) : MemLp (C j) 2 (volume.restrict K) := by
    exact memLp_finsetSum _ (fun i _ => memLp_mul_coefficient_on_compact hK
      ((hDA i j).continuousOn.mono hKW) (hD i))
  have hdC (j : ι) : MemLp (dC j) 2 (volume.restrict K) := by
    exact memLp_finsetSum _ (fun i _ =>
      (memLp_mul_coefficient_on_compact hK ((hD2 i j).continuousOn.mono hKW) (hD i)).add
        (memLp_mul_coefficient_on_compact hK ((hDA i j).continuousOn.mono hKW)
          (hdD j i)))
  have hwC (j : ι) : HasWeakDirectionalDerivativeOn K (b j) (C j) (dC j) := by
    apply HasWeakDirectionalDerivativeOn.finset_sum Finset.univ _ _
      (fun i _ => memLp_mul_coefficient_on_compact hK
        ((hDA i j).continuousOn.mono hKW) (hD i))
      (fun i _ =>
        (memLp_mul_coefficient_on_compact hK
          ((hD2 i j).continuousOn.mono hKW)
          (hD i)).add
          (memLp_mul_coefficient_on_compact hK ((hDA i j).continuousOn.mono hKW)
            (hdD j i)))
      (fun i _ =>
        (hweak j i).mul_coefficient hW hKW (hD i) (hdD j i) (hDA i j))
  have he := weak_divergence_coefficient_derivative b hK hW hKW (b k) A D
    (fun i => dD k i) F dF hA hD (fun i => hdD k i)
    (fun i => hweak k i) hF hPDE
  have hp (j : ι) : MemLp (P j) 2 (volume.restrict K) :=
    memLp_finsetSum _ (fun i _ => memLp_mul_coefficient_on_compact hK
      ((hA i j).continuousOn.mono hKW) (hdD k i))
  obtain ⟨hg, heq⟩ := weak_divergence_remove_commutator b K P C dC dF
    hp hC hdC hdF hwC (by
      intro φ hφ hc hs
      have hh := he.2 φ hφ hc hs
      have hsum (j : ι) (z : E) :
          (∑ i, (fderiv ℝ (fun y => A y i j) z (b k) * D i z +
            A z i j * dD k i z)) = P j z + C j z := by
        dsimp [P, C]
        rw [Finset.sum_add_distrib]
        exact add_comm _ _
      simp_rw [hsum] at hh
      exact hh)
  refine ⟨?_, ?_⟩
  · simpa [dC] using hg
  · intro φ hφ hc hs
    simpa [P, dC] using heq φ hφ hc hs

/-! ## Localized extraction and the finite-jet successor -/

theorem HasWeakDirectionalDerivativeOn.congr_left_ae
    {S : Set E} {v : E} {u u' du : E → ℝ}
    (hEq : u =ᵐ[volume.restrict S] u')
    (h : HasWeakDirectionalDerivativeOn S v u' du) :
    HasWeakDirectionalDerivativeOn S v u du := by
  intro φ hφ hc hs
  calc
    (∫ z in S, u z * fderiv ℝ φ z v) =
        ∫ z in S, u' z * fderiv ℝ φ z v := by
      apply integral_congr_ae
      exact hEq.mul EventuallyEq.rfl
    _ = -(∫ z in S, du z * φ z) := h φ hφ hc hs

theorem LocalL2DerivativeJet.gain_of_local_weak_derivatives
    {ι : Type*} {b : ι → E} {K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n)
    (hnew : ∀ w : List ι, w.length = n → ∀ i : ι, ∃ g : Lp ℝ 2 (volume : Measure E),
      HasWeakDirectionalDerivativeOn K (b i) (J.value w) g) :
    ∃ J' : LocalL2DerivativeJet b K (n + 1),
      ∀ w : List ι, w.length ≤ n → J'.value w = J.value w := by
  classical
  have hex (w : List ι) (i : ι) : ∃ g : Lp ℝ 2 (volume : Measure E),
      w.length = n → HasWeakDirectionalDerivativeOn K (b i) (J.value w) g := by
    by_cases hw : w.length = n
    · obtain ⟨g, hg⟩ := hnew w hw i
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun hh => (hw hh).elim⟩
  choose g hg using hex
  let V : List ι → Lp ℝ 2 (volume : Measure E) := fun w =>
    match w with
    | [] => J.value []
    | i :: t => if t.length = n then g t i else J.value (i :: t)
  have hV (w : List ι) (hw : w.length ≤ n) : V w = J.value w := by
    cases w with
    | nil => rfl
    | cons i t =>
      have ht : t.length ≠ n := by
        simp only [List.length_cons] at hw
        omega
      simp [V, ht]
  refine ⟨⟨V, ?_⟩, hV⟩
  intro w hw i
  have hwle : w.length ≤ n := by omega
  rw [hV w hwle]
  by_cases he : w.length = n
  · have hv : V (i :: w) = g w i := by simp [V, he]
    rw [hv]
    exact hg w i he
  · have hwl : w.length < n := by omega
    have hv : V (i :: w) = J.value (i :: w) := by simp [V, he]
    rw [hv]
    exact J.weak w hwl i

theorem exists_local_weak_derivative_of_weighted_quotient_bound
    {ι : Type*} [Fintype ι] {S : Set E}
    (hS : IsCompact S) (D : Lp ℝ 2 (volume : Measure E)) (v : E)
    {η : E → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hηb : ∀ᵐ x ∂(volume : Measure E), ‖η x‖ ≤ 1)
    (hηS : ∀ x ∈ S, η x = 1)
    (L : ℝ) (hL : 0 ≤ L)
    (hLq : ∀ (x : E) (h : ℝ), h ≠ 0 →
      ‖h⁻¹ * (η (x + h • v) - η x)‖ ≤ L)
    (C δ : ℝ) (hδ : 0 < δ) (i : ι)
    (hbound : ∀ h : ℝ, h ≠ 0 → |h| < δ →
      ∃ r : Lp (EuclideanSpace ℝ ι) 2 (volume : Measure E),
        (∀ᵐ x ∂(volume : Measure E),
          r x i =
            η x * directionalDifferenceQuotient D v h x) ∧ ‖r‖ ≤ C) :
    ∃ g : Lp ℝ 2 (volume : Measure E),
      ‖g‖ ≤ C + L * ‖D‖ ∧
      HasWeakDirectionalDerivativeOn S v D g := by
  classical
  let N := boundedL2Multiplier η hη.continuous.aestronglyMeasurable 1 hηb
  have hN (u : Lp ℝ 2 (volume : Measure E)) :
      N u =ᵐ[volume] (fun x => η x * u x) :=
    boundedL2Multiplier_ae_eq _ _ _ _ u
  let q := N D
  have hqD : q =ᵐ[volume.restrict S] (D : E → ℝ) := by
    filter_upwards [ae_restrict_of_ae (hN D), ae_restrict_mem hS.measurableSet]
      with x hx hxs
    rw [hx, hηS x hxs, one_mul]
  have hwb : ∀ h : ℝ, h ≠ 0 → |h| < δ →
      ‖directionalDifferenceQuotient q v h‖ ≤ C + L * ‖D‖ := by
    intro h hh hsmall
    obtain ⟨r, hr, hrB⟩ := hbound (-h) (neg_ne_zero.mpr hh) (by simpa using hsmall)
    have hn : ‖N (directionalDifferenceQuotient D v (-h))‖ ≤ C := by
      apply le_trans (b := ‖r‖) _ hrB
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hN (directionalDifferenceQuotient D v (-h)), hr]
        with x hn hr
      have he : N (directionalDifferenceQuotient D v (-h)) x = r x i := by
        rw [hn, hr]
      rw [he]
      exact PiLp.norm_apply_le _ i
    have hstep : ∀ᵐ x ∂(volume : Measure E),
        ‖h⁻¹ * (η (x + h • v) - η x)‖ ≤ L :=
      Eventually.of_forall (fun x => hLq x h hh)
    exact (norm_differenceQuotient_cutoff_le
      η hη.continuous.aestronglyMeasurable 1 hηb D v h L hstep).trans
      (add_le_add hn le_rfl)
  obtain ⟨g, hg, hweak⟩ := exists_weakDerivative_of_differenceQuotient_bound_on_ball
    q v (C + L * ‖D‖) δ hδ hwb
  have hweak' : HasWeakDirectionalDerivativeOn S v q g := by
    apply hasWeakDirectionalDerivativeOn_of_global_test_identity S v q g
    intro φ hφ hc hs
    exact hweak φ (hφ.of_le (by decide)) hc
  exact ⟨g, hg, HasWeakDirectionalDerivativeOn.congr_left_ae hqD.symm hweak'⟩

/-! ## Weak-addition infrastructure -/

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

namespace WeakExpr

variable {ι : Type uι} [Fintype ι] {K : Set E} {n : ℕ}
  {b : ι → E} {J : LocalL2DerivativeJet b K n}
  {A : E → ι → ι → ℝ} {F : E → ℝ}

theorem memLp_eval
    (hK : IsCompact K) {W : Set E} (hW : IsOpen W) (hKW : K ⊆ W)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) W)
    (hF : ContDiffOn ℝ ∞ F W)
    (p : WeakExpr b J A F) (hp : p.jetBound ≤ n) :
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
  | sum p ih =>
      simpa [eval] using
        (memLp_finsetSum Finset.univ (fun i hi =>
          ih i (le_trans (jetBound_sum_le p i) hp)))

theorem weak_derivative_eval
    (hK : IsCompact K) {W : Set E} (hW : IsOpen W) (hKW : K ⊆ W)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) W)
    (hF : ContDiffOn ℝ ∞ F W)
    (p : WeakExpr b J A F) (hp : p.jetBound + 1 ≤ n) (k : ι) :
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

end WeakExpr

/-! ## Differentiating a coefficient equation with weak forcing -/

theorem LocalL2DerivativeJet.exists_scalar_forcing_differentiated_equation_of_weak_forcing
    {ι : Type*} [Fintype ι] {b : ι → E} {K W : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) (w : List ι) (hw : w.length + 1 < n)
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (k : ι) (A : E → ι → ι → ℝ) (F dF : E → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) W)
    (hdF : MemLp dF 2 (volume.restrict K))
    (hF : HasWeakDirectionalDerivativeOn K (b k) F dF)
    (hPDE : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (∑ i, A z i j * J.value (i :: w) z) *
        fderiv ℝ φ z (b j)) = -(∫ z in K, F z * φ z)) :
    MemLp (fun z => dF z - ∑ j, ∑ i,
      (fderiv ℝ (fun y => fderiv ℝ (fun x => A x i j) y (b k)) z (b j) *
        J.value (i :: w) z +
       fderiv ℝ (fun y => A y i j) z (b k) * J.value (j :: i :: w) z)) 2
      (volume.restrict K) ∧
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (∑ i, A z i j * J.value (k :: i :: w) z) *
        fderiv ℝ φ z (b j)) = -(∫ z in K, (dF z - ∑ j, ∑ i,
          (fderiv ℝ (fun y => fderiv ℝ (fun x => A x i j) y (b k)) z (b j) *
            J.value (i :: w) z +
           fderiv ℝ (fun y => A y i j) z (b k) * J.value (j :: i :: w) z)) * φ z) := by
  let P := fun j z => ∑ i, A z i j * J.value (k :: i :: w) z
  let C := fun j z => ∑ i, fderiv ℝ (fun y => A y i j) z (b k) * J.value (i :: w) z
  let dC := fun j z => ∑ i,
    (fderiv ℝ (fun y => fderiv ℝ (fun x => A x i j) y (b k)) z (b j) *
      J.value (i :: w) z +
     fderiv ℝ (fun y => A y i j) z (b k) * J.value (j :: i :: w) z)
  have hc := fun j => J.commutator_weak_derivative w hw hK hW hKW k j A hA
  have hp (j : ι) : MemLp (P j) 2 (volume.restrict K) :=
    memLp_finsetSum _ (fun i _ => memLp_mul_coefficient_on_compact hK
      ((hA i j).continuousOn.mono hKW) ((Lp.memLp (J.value (k :: i :: w))).restrict K))
  have hdm (j : ι) : MemLp (dC j) 2 (volume.restrict K) := (hc j).2.1
  have he := weak_divergence_coefficient_derivative b hK hW hKW (b k) A
    (fun i => J.value (i :: w)) (fun i => J.value (k :: i :: w)) F dF hA
    (fun i => (Lp.memLp (J.value (i :: w))).restrict K)
    (fun i => (Lp.memLp (J.value (k :: i :: w))).restrict K)
    (fun i => J.weak (i :: w) (by simpa using hw) k) hF hPDE
  have he' : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (P j z + C j z) * fderiv ℝ φ z (b j)) =
        -(∫ z in K, dF z * φ z) := by
    intro φ hφ hcφ hs
    have hh := he.2 φ hφ hcφ hs
    have ha (j : ι) (z : E) :
        (∑ i, (fderiv ℝ (fun y => A y i j) z (b k) * J.value (i :: w) z +
          A z i j * J.value (k :: i :: w) z)) = P j z + C j z := by
      rw [Finset.sum_add_distrib]
      exact add_comm _ _
    simp_rw [ha] at hh
    exact hh
  obtain ⟨hg, heq⟩ := weak_divergence_remove_commutator b K P C dC dF
    hp (fun j => (hc j).1) (fun j => hdm j) hdF (fun j => (hc j).2.2) he'
  refine ⟨hg, ?_⟩
  intro φ hφ hcφ hs
  simpa [P, dC] using heq φ hφ hcφ hs

end AlmostSchur

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## Restriction and reindexing lemmas used by the interior induction -/

theorem HasWeakDirectionalDerivativeOn.restrict
    {S K : Set E} {v : E} {u du : E → ℝ}
    (h : HasWeakDirectionalDerivativeOn K v u du) (hSK : S ⊆ K) :
    HasWeakDirectionalDerivativeOn S v u du := by
  intro φ hφ hc hs
  have hzeroL (z : E) (hz : z ∉ S) : u z * fderiv ℝ φ z v = 0 := by
    simp [fderiv_of_notMem_tsupport ℝ (fun hh => hz (hs hh))]
  have hzeroR (z : E) (hz : z ∉ S) : du z * φ z = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hz (hs hh)), mul_zero]
  have hzeroLK : ∀ z ∉ K, u z * fderiv ℝ φ z v = 0 :=
    fun z hz => hzeroL z (fun hzs => hz (hSK hzs))
  have hzeroRK : ∀ z ∉ K, du z * φ z = 0 :=
    fun z hz => hzeroR z (fun hzs => hz (hSK hzs))
  calc
    (∫ z in S, u z * fderiv ℝ φ z v) = ∫ z, u z * fderiv ℝ φ z v :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hzeroL
    _ = ∫ z in K, u z * fderiv ℝ φ z v :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzeroLK).symm
    _ = -(∫ z in K, du z * φ z) := h φ hφ hc (hs.trans hSK)
    _ = -(∫ z, du z * φ z) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroRK]
    _ = -(∫ z in S, du z * φ z) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroR]

def LocalL2DerivativeJet.restrict
    {ι : Type*} {b : ι → E} {S K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) (hSK : S ⊆ K) :
    LocalL2DerivativeJet b S n :=
  ⟨J.value, fun w hw i => (J.weak w hw i).restrict hSK⟩

theorem LocalL2DerivativeJet.restrict_value
    {ι : Type*} {b : ι → E} {S K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) (hSK : S ⊆ K) (w : List ι) :
    (J.restrict hSK).value w = J.value w := rfl

theorem weakCoefficientEquation.restrict
    {ι : Type*} [Fintype ι] {b : ι → E} {S K : Set E} {n : ℕ}
    {A : E → ι → ι → ℝ} {J : LocalL2DerivativeJet b K n} {w : List ι}
    {G : E → ℝ} (h : weakCoefficientEquation A J w G) (hSK : S ⊆ K) :
    weakCoefficientEquation A (J.restrict hSK) w G := by
  intro φ hφ hc hs
  have hzeroL (j : ι) (z : E) (hz : z ∉ S) :
      (∑ i, A z i j * J.value (i :: w) z) * fderiv ℝ φ z (b j) = 0 := by
    simp [fderiv_of_notMem_tsupport ℝ (fun hh => hz (hs hh))]
  have hzeroR (z : E) (hz : z ∉ S) : G z * φ z = 0 := by
    simp [image_eq_zero_of_notMem_tsupport (fun hh => hz (hs hh))]
  have hzeroLK (j : ι) (z : E) (hz : z ∉ K) :
      (∑ i, A z i j * J.value (i :: w) z) * fderiv ℝ φ z (b j) = 0 :=
    hzeroL j z (fun hzs => hz (hSK hzs))
  have hzeroRK (z : E) (hz : z ∉ K) : G z * φ z = 0 :=
    hzeroR z (fun hzs => hz (hSK hzs))
  calc
    (∑ j, ∫ z in S, (∑ i, A z i j * (J.restrict hSK).value (i :: w) z) *
        fderiv ℝ φ z (b j)) =
        ∑ j, ∫ z, (∑ i, A z i j * J.value (i :: w) z) *
          fderiv ℝ φ z (b j) := by
      apply Finset.sum_congr rfl
      intro j hj
      change (∫ z in S, (∑ i, A z i j * J.value (i :: w) z) *
        fderiv ℝ φ z (b j)) = _
      exact setIntegral_eq_integral_of_forall_compl_eq_zero (hzeroL j)
    _ = ∑ j, ∫ z in K, (∑ i, A z i j * J.value (i :: w) z) *
        fderiv ℝ φ z (b j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hzeroLK j)).symm
    _ = -(∫ z in K, G z * φ z) := h φ hφ hc (hs.trans hSK)
    _ = -(∫ z, G z * φ z) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroRK]
    _ = -(∫ z in S, G z * φ z) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroR]

namespace WeakExpr

variable {ι : Type*} [Fintype ι] {K K' : Set E} {n : ℕ}
  {b : ι → E} {J : LocalL2DerivativeJet b K n}
  {J' : LocalL2DerivativeJet b K' n}
  {A : E → ι → ι → ℝ} {F : E → ℝ}

/-- Reindex an expression along a replacement of its weak jet.  The
expression tree is unchanged; only the jet used by its evaluation changes. -/
def reindex : WeakExpr b J A F → WeakExpr b J' A F
  | .zero => .zero
  | .smoothF w => .smoothF w
  | .coeff i j w => .coeff i j w
  | .jet w => .jet w
  | .add p q => .add (reindex p) (reindex q)
  | .sub p q => .sub (reindex p) (reindex q)
  | .coeffMul i j w p => .coeffMul i j w (reindex p)
  | .sum p => .sum (fun i => reindex (p i))

theorem jetBound_reindex (p : WeakExpr b J A F) :
    jetBound (reindex (J' := J') p) = jetBound p := by
  induction p with
  | zero | smoothF _ | coeff _ _ _ | jet _ => rfl
  | add p q hp hq => simp [reindex, jetBound, hp, hq]
  | sub p q hp hq => simp [reindex, jetBound, hp, hq]
  | coeffMul i j w p hp => simp [reindex, jetBound, hp]
  | sum p ih =>
      simp only [reindex, jetBound]
      congr 1
      funext i
      exact ih i

theorem eval_reindex_eq
    (p : WeakExpr b J A F)
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
  | sum p ih =>
      funext z
      simp only [eval, reindex]
      apply Finset.sum_congr rfl
      intro i hi
      exact congrFun (ih i (le_trans (jetBound_sum_le p i) hp)) z

theorem eval_reindex_eq_all
    (p : WeakExpr b J A F)
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
  | sum p ih =>
      funext z
      simp only [eval, reindex]
      apply Finset.sum_congr rfl
      intro i hi
      exact congrFun (ih i) z

theorem reindex_deriv (k : ι) (p : WeakExpr b J A F) :
    reindex (J' := J') (deriv k p) = deriv k (reindex (J' := J') p) := by
  induction p with
  | zero | smoothF _ | coeff _ _ _ | jet _ => rfl
  | add p q hp hq => simp [deriv, reindex, hp, hq]
  | sub p q hp hq => simp [deriv, reindex, hp, hq]
  | coeffMul i j w p hp => simp [deriv, reindex, hp]
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

end WeakExpr

end AlmostSchur

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A finite jet together with the transposed coefficient equation at every
level for which that equation only uses fields already present in the jet. -/
def WeakPoissonHierarchy
    {ι : Type*} [Fintype ι] {b : ι → E} {K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) (A : E → ι → ι → ℝ) (F : E → ℝ) : Prop :=
  ∀ w : List ι, w.length + 1 < n →
    weakCoefficientEquation A J w
      (WeakExpr.forcing (b := b) (J := J) (A := A) (F := F) w).eval

theorem WeakPoissonHierarchy.restrict
    {ι : Type*} [Fintype ι] {b : ι → E} {S K : Set E} {n : ℕ}
    {J : LocalL2DerivativeJet b K n} {A : E → ι → ι → ℝ} {F : E → ℝ}
    (h : WeakPoissonHierarchy J A F) (hSK : S ⊆ K) :
    WeakPoissonHierarchy (J.restrict hSK) A F := by
  intro w hw
  have h0 := weakCoefficientEquation.restrict (h w hw) hSK
  rw [WeakExpr.eval_forcing_restrict J hSK A F w]
  exact h0

end AlmostSchur
/-!
# Arbitrary finite-order weak Poisson jets

This is the elliptic induction missing from `WeakPoissonAllOrderJets`.  The
successor is built from the actual local H² quotient estimate: coefficient
quotients come from smoothness on a convex compact set, the graph is built
from the current weak jet, and nested compact cutoffs keep every test inside
the preceding interior.  In particular, no difference-quotient bound for a
jet field is an input.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators Convolution Pointwise Matrix.Norms.Elementwise

namespace AlmostSchur

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
universe uE uι

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-! ## Smooth approximation of a compactly supported C¹ graph -/

-- The Euclidean Rellich--Kondrachov implementation uses the canonical Borel
-- structure.  These local instances make its L² classes definitionally line
-- up with the ambient classes used by the Poisson files.
section AWPJDensity

local instance awpjMeasurableSpace : MeasurableSpace E := borel E
local instance awpjBorelSpace : BorelSpace E := ⟨rfl⟩
local instance awpjOpensMeasurableSpace : OpensMeasurableSpace E := by
  infer_instance
local instance awpjMeasurableAdd : MeasurableAdd E := by
  infer_instance

private lemma awpj_tendsto_translateL2_zero
    (F : E →₂[(volume : Measure E)] ℝ) :
    Tendsto (fun t : E => translateL2 (μ := (volume : Measure E)) t F)
      (𝓝 (0 : E)) (𝓝 F) := by
  let g : E → C(E, E) := fun t => ContinuousMap.addRight t
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : E × E => p.2 + p.1)
    exact continuous_snd.add continuous_fst
  have hmp : ∀ t : E,
      MeasurePreserving (g t) (volume : Measure E) (volume : Measure E) := by
    intro t
    exact MeasureTheory.measurePreserving_add_right (μ := (volume : Measure E)) t
  have hcomp : Continuous (fun t : E =>
      MeasureTheory.Lp.compMeasurePreserving (g t) (hmp t) F) :=
    (continuous_const : Continuous (fun _ : E => F)).compMeasurePreservingLp
      hg hmp (by norm_num)
  have hcomp0 :
      MeasureTheory.Lp.compMeasurePreserving (g 0) (hmp 0) F = F := by
    apply MeasureTheory.Lp.ext
    filter_upwards [MeasureTheory.Lp.coeFn_compMeasurePreserving F (hmp 0)] with x hx
    simpa [g, Function.comp_def] using hx
  have htrans (t : E) :
      translateL2 (μ := (volume : Measure E)) t F =
        MeasureTheory.Lp.compMeasurePreserving (g t) (hmp t) F := by
    apply MeasureTheory.Lp.ext
    filter_upwards [translateL2_ae_eq (μ := (volume : Measure E)) t F,
      MeasureTheory.Lp.coeFn_compMeasurePreserving F (hmp t)] with x hx ht
    have ht' :
        (MeasureTheory.Lp.compMeasurePreserving (g t) (hmp t) F : E → ℝ) x =
          (F : E → ℝ) (x + t) := by
      simpa [g, Function.comp_def] using ht
    exact hx.trans ht'.symm
  have htransfun :
      (fun t : E => translateL2 (μ := (volume : Measure E)) t F) =
      (fun t : E => MeasureTheory.Lp.compMeasurePreserving (g t) (hmp t) F) :=
    funext htrans
  have hlim : Tendsto (fun t : E =>
      MeasureTheory.Lp.compMeasurePreserving (g t) (hmp t) F) (𝓝 (0 : E))
        (𝓝 (MeasureTheory.Lp.compMeasurePreserving (g 0) (hmp 0) F)) :=
    hcomp.continuousAt
  rw [hcomp0] at hlim
  rw [htransfun]
  exact hlim

private lemma awpj_extendByZeroL2_eq_toLp_of_support
    {S : Set E} (hS : IsCompact S) (f : E → ℝ)
    (hf : MemLp f 2 (volume : Measure E)) (hsupp : Function.support f ⊆ S) :
    extendByZeroL2 (E := E) (K := S) hS.measurableSet ((hf.restrict S).toLp f) =
      hf.toLp f := by
  apply MeasureTheory.Lp.ext
  have hrestrict :
      ((hf.restrict S).toLp f : E → ℝ) =ᵐ[(volume : Measure E).restrict S] f :=
    (hf.restrict S).coeFn_toLp
  have hext :
      (extendByZeroL2 (E := E) (K := S) hS.measurableSet
        ((hf.restrict S).toLp f) : E → ℝ) =ᵐ[volume]
        extendByZeroFun (E := E) (K := S) ((hf.restrict S).toLp f) :=
    extendByZeroL2_ae_eq (E := E) (K := S) hS.measurableSet ((hf.restrict S).toLp f)
  have hrestrict' : ∀ᵐ x : E ∂(volume : Measure E),
      x ∈ S → ((hf.restrict S).toLp f : E → ℝ) x = f x :=
    (MeasureTheory.ae_restrict_iff' hS.measurableSet).1 hrestrict
  have hfull : ∀ᵐ x : E ∂(volume : Measure E),
      (hf.toLp f : E → ℝ) x = f x := hf.coeFn_toLp
  filter_upwards [hext, hrestrict', hfull] with x hx hfx hff
  by_cases hxs : x ∈ S
  · rw [hx]
    simp only [extendByZeroFun, Set.indicator_of_mem hxs]
    exact (hfx hxs).trans hff.symm
  · rw [hx]
    simp only [extendByZeroFun, Set.indicator, hxs, ↓reduceIte]
    by_contra hne
    apply hxs
    apply hsupp
    intro hzero
    apply hne
    rw [hff, hzero]

private theorem awpj_exists_contDiff_kernel
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ x, 0 ≤ ψ x) ∧ (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
        tsupport ψ ⊆ Metric.ball (0 : E) δ := by
  classical
  have hs : (Metric.ball (0 : E) δ) ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds _ hδ
  rcases exists_contDiff_tsupport_subset (n := ⊤)
    (E := E) (s := Metric.ball (0 : E) δ) (x := (0 : E)) hs with
    ⟨f, hf_tsupp, hf_cs, hf_smooth, hf_range, hf0⟩
  have hf_cont : Continuous f := hf_smooth.continuous
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    exact (hf_range ⟨x, rfl⟩).1
  have hf0_ne : f (0 : E) ≠ 0 := by simp [hf0]
  have hIpos : 0 < ∫ x, f x ∂(volume : Measure E) := by
    simpa using!
      (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
        (μ := (volume : Measure E)) hf_cont hf_cs hf_nonneg hf0_ne)
  set I : ℝ := ∫ x, f x ∂(volume : Measure E)
  have hI0 : I ≠ 0 := ne_of_gt hIpos
  have hIpos' : 0 < I := by simpa [I] using hIpos
  let ψ : E → ℝ := fun x => I⁻¹ * f x
  have hψsmooth : ContDiff ℝ ∞ ψ := by
    simpa [ψ] using (contDiff_const.mul hf_smooth)
  have hψcs : HasCompactSupport ψ := by
    rw [show ψ = (fun _x : E => I⁻¹) * f by funext x; rfl]
    exact HasCompactSupport.smul_left (f := fun _x : E => I⁻¹) (f' := f) hf_cs
  have hψ0 : ∀ x, 0 ≤ ψ x := by
    intro x
    exact mul_nonneg (inv_nonneg.mpr hIpos'.le) (hf_nonneg x)
  have hψint : ∫ x, ψ x ∂(volume : Measure E) = 1 := by
    have hmul : (∫ x, ψ x ∂(volume : Measure E)) = I⁻¹ * I := by
      simpa [ψ, I] using
        (MeasureTheory.integral_const_mul (μ := (volume : Measure E))
          (r := I⁻¹) (f := f))
    rw [hmul]
    exact inv_mul_cancel₀ hI0
  have hψ_tsupp : tsupport ψ ⊆ Metric.ball (0 : E) δ := by
    have hsub : tsupport ψ ⊆ tsupport f := by
      simpa [ψ, smul_eq_mul] using
        (tsupport_smul_subset_right (f := fun _x : E => I⁻¹) (g := f))
    exact hsub.trans hf_tsupp
  exact ⟨ψ, hψsmooth, hψcs, hψ0, hψint, hψ_tsupp⟩

private lemma awpj_smoothL2_kernel_tendsto
    {S : Set E} (hS : IsCompact S) (f : E → ℝ)
    (hf : MemLp f 2 (volume : Measure E)) (hsupp : Function.support f ⊆ S)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrt : Tendsto r atTop (𝓝 0))
    (ψ : ℕ → E → ℝ)
    (hψ : ∀ n, Continuous (ψ n) ∧ HasCompactSupport (ψ n) ∧
      (∀ x, 0 ≤ ψ n x) ∧ (∫ x, ψ n x ∂(volume : Measure E) = 1) ∧
      tsupport (ψ n) ⊆ Metric.ball (0 : E) (r n)) :
    Tendsto (fun n => smoothL2 (E := E) (K := S) (ψ n) hS hS.measurableSet
      (hψ n).1 (hψ n).2.1 ((hf.restrict S).toLp f)) atTop
      (𝓝 (hf.toLp f)) := by
  let uS : Lp ℝ 2 (volume.restrict S) := (hf.restrict S).toLp f
  have hExt : extendByZeroL2 (E := E) (K := S) hS.measurableSet uS = hf.toLp f := by
    exact awpj_extendByZeroL2_eq_toLp_of_support hS f hf hsupp
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htrans : Tendsto (fun t : E =>
      translateL2 (μ := (volume : Measure E)) (-t) (hf.toLp f)) (𝓝 (0 : E))
    (𝓝 (hf.toLp f)) := by
    have hneg : Tendsto (fun t : E => -t) (𝓝 (0 : E)) (𝓝 (0 : E)) := by
      have hneg' : Tendsto (fun t : E => -t) (𝓝 (0 : E))
          (𝓝 (-(0 : E))) := continuous_neg.continuousAt
      simpa only [neg_zero] using hneg'
    simpa [Function.comp_def] using
      (awpj_tendsto_translateL2_zero (F := hf.toLp f)).comp hneg
  have hev : ∀ᶠ t : E in 𝓝 (0 : E),
      dist (translateL2 (μ := (volume : Measure E)) (-t) (hf.toLp f))
        (hf.toLp f) < ε / 2 :=
    htrans.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  obtain ⟨δ, hδ, hδmod⟩ := (Metric.eventually_nhds_iff.mp hev)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hrt) δ hδ
  refine ⟨N, ?_⟩
  intro n hn
  have hrδ : r n < δ := by
    have h := hN n hn
    simpa [dist_zero_right, abs_of_pos (hr n)] using h
  have hmod : ∀ t : E, t ∈ Metric.ball (0 : E) δ →
      ‖translateL2 (μ := (volume : Measure E)) (-t) (hf.toLp f) - hf.toLp f‖ ≤ ε / 2 := by
    intro t ht
    have hlt := hδmod (by simpa [Metric.mem_ball] using ht)
    exact le_of_lt (by simpa [dist_eq_norm] using hlt)
  have hψn := hψ n
  have hψsupp : tsupport (ψ n) ⊆ Metric.ball (0 : E) δ :=
    hψn.2.2.2.2.trans (Metric.ball_subset_ball (le_of_lt hrδ))
  have hint := integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
    (E := E) hψn.1 hψn.2.1 hψn.2.2.1 hψn.2.2.2.1
    (hη := by positivity) hψsupp (hf.toLp f) hmod
  have hint' : ∫ t,
        ‖translateL2 (μ := (volume : Measure E)) (-t) (extendByZeroL2
          (E := E) (K := S) hS.measurableSet uS) - extendByZeroL2
          (E := E) (K := S) hS.measurableSet uS‖ ^ 2
      ∂kernelMeasure (E := E) (ψ n) ≤ (ε / 2) ^ 2 := by
    simpa only [hExt] using hint
  have hsq := norm_sq_smoothL2_sub_extendByZeroL2_le_integral_norm_sq_translateL2_sub_extendByZeroL2
    (E := E) (K := S) hS hS.measurableSet (ψ := ψ n) hψn.1 hψn.2.1
    hψn.2.2.1 hψn.2.2.2.1 uS
  have hsq' : ‖smoothL2 (E := E) (K := S) (ψ n) hS hS.measurableSet
      hψn.1 hψn.2.1 uS - hf.toLp f‖ ^ 2 ≤ (ε / 2) ^ 2 := by
    rw [← hExt]
    exact hsq.trans hint'
  have hle : ‖smoothL2 (E := E) (K := S) (ψ n) hS hS.measurableSet
      hψn.1 hψn.2.1 uS - hf.toLp f‖ ≤ ε / 2 := by
    nlinarith [sq_nonneg (‖smoothL2 (E := E) (K := S) (ψ n) hS hS.measurableSet
      hψn.1 hψn.2.1 uS - hf.toLp f‖)]
  simpa [dist_eq_norm] using lt_of_le_of_lt hle (by linarith)

end AWPJDensity

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance awpjMainMeasurableSpace : MeasurableSpace E := borel E
local instance awpjMainBorelSpace : BorelSpace E := ⟨rfl⟩
local instance awpjMainOpensMeasurableSpace : OpensMeasurableSpace E := by
  infer_instance
local instance awpjMainMeasurableAdd : MeasurableAdd E := by
  infer_instance

def smoothSupportedTestGraph {ι : Type uι} (b : ι → E) (U : Set E) :
    Set (Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))) :=
  {p | ∃ φ : E → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
    p.1 =ᵐ[volume] φ ∧ ∀ i, p.2 i =ᵐ[volume] (fun z => fderiv ℝ φ z (b i))}

theorem c1SupportedTestGraph_mem_closure_smoothSupportedTestGraph
    {ι : Type uι} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {S K : Set E} (hS : IsCompact S) (hK : IsCompact K)
    (hSK : S ⊆ interior K) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ S) :
    (((hφ.continuous.memLp_of_hasCompactSupport hcφ).toLp φ,
      fun i => (((hφ.continuous_fderiv (by norm_num)).clm_apply
        (continuous_const (y := b i))).memLp_of_hasCompactSupport
          (hcφ.fderiv_apply ℝ (b i))).toLp (fun z => fderiv ℝ φ z (b i))) :
      Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))) ∈
      closure (smoothSupportedTestGraph (fun i => b i) K) := by
  classical
  have hφ0 : MemLp φ 2 (volume : Measure E) :=
    hφ.continuous.memLp_of_hasCompactSupport hcφ
  have hφd (i : ι) : MemLp (fun z => fderiv ℝ φ z (b i)) 2
      (volume : Measure E) :=
    ((hφ.continuous_fderiv (by norm_num)).clm_apply
      (continuous_const (y := b i))).memLp_of_hasCompactSupport
        (hcφ.fderiv_apply ℝ (b i))
  obtain ⟨ε₀, hε₀, hmargin⟩ := exists_uniform_translation_margin hS
    isOpen_interior hSK
  let r : ℕ → ℝ := fun m => min (ε₀ / 2) (((m : ℝ) + 1)⁻¹)
  have hr (m : ℕ) : 0 < r m := by
    exact lt_min (by linarith) (inv_pos.mpr (by positivity))
  have hrt : Tendsto r atTop (𝓝 0) := by
    have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hplus : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right atTop 1 hnat
    have hinv : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hplus
    have hmin := Filter.Tendsto.min
      (f := fun _ : ℕ => ε₀ / 2) (g := fun m : ℕ => ((m : ℝ) + 1)⁻¹)
      tendsto_const_nhds hinv
    simpa [r, min_eq_right (le_of_lt (by linarith : 0 < ε₀ / 2))] using hmin
  choose ψ hψ using fun m => awpj_exists_contDiff_kernel (E := E) (hr m)
  let u₀ : Lp ℝ 2 (volume : Measure E) := hφ0.toLp φ
  let d : ι → E → ℝ := fun i => fun z => fderiv ℝ φ z (b i)
  have hφdi (i : ι) : MemLp (d i) 2 (volume : Measure E) := by
    simpa [d] using hφd i
  let du : ι → Lp ℝ 2 (volume : Measure E) := fun i =>
    (hφdi i).toLp (d i)
  have hu₀ : (u₀ : E → ℝ) =ᵐ[(volume : Measure E)] φ := by
    simpa [u₀] using hφ0.coeFn_toLp
  have hdu (i : ι) : (du i : E → ℝ) =ᵐ[(volume : Measure E)] d i := by
    simpa [du, d] using (hφd i).coeFn_toLp
  have hsupp₀ : Function.support φ ⊆ S := by
    exact (subset_closure : Function.support φ ⊆ closure (Function.support φ)).trans
      (by simpa [tsupport] using hsφ)
  have hsuppd (i : ι) : Function.support (d i) ⊆ S := by
    simpa [d] using
      ((subset_closure : Function.support (fun z => fderiv ℝ φ z (b i)) ⊆
        closure (Function.support (fun z => fderiv ℝ φ z (b i)))).trans
        ((tsupport_fderiv_apply_subset ℝ (b i)).trans hsφ))
  have hweak (i : ι) : HasWeakDirectionalDerivativeOn Set.univ
      (b i) (u₀ : E → ℝ) (du i : E → ℝ) := by
    apply hasWeakDirectionalDerivativeOn_of_global_test_identity Set.univ
      (b i) (u₀ : E → ℝ) (du i : E → ℝ)
    intro θ hθ hcθ _
    have hIBP := integral_mul_fderiv_openDomain (μ := (volume : Measure E))
      (U := Set.univ) isOpen_univ φ θ hφ.contDiffOn
      (hθ.of_le (by norm_num)) hcθ (subset_univ _) (b i)
    calc
      (∫ z, u₀ z * fderiv ℝ θ z (b i)) =
          ∫ z, φ z * fderiv ℝ θ z (b i) := by
        apply integral_congr_ae
        filter_upwards [hu₀] with z hz
        rw [hz]
      _ = -(∫ z, d i z * θ z) := by simpa [d] using hIBP
      _ = -(∫ z, (du i : E → ℝ) z * θ z) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hdu i] with z hz
        rw [hz]
  have hmul : ContinuousLinearMap.lsmul ℝ ℝ = ContinuousLinearMap.mul ℝ ℝ := by
    ext x y
    simp [smul_eq_mul]
  have hconv (f : E → ℝ) (hf : MemLp f 2 (volume : Measure E))
      (hsupp : Function.support f ⊆ S) (m : ℕ) :
      smoothFun (E := E) (K := S) (ψ m)
          ((hf.restrict S).toLp f) =
        ((hf.toLp f : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (ψ m)) := by
    have hExt : extendByZeroL2 (E := E) (K := S) hS.measurableSet
        ((hf.restrict S).toLp f) = hf.toLp f := by
      exact awpj_extendByZeroL2_eq_toLp_of_support hS f hf hsupp
    have hzero :
        (extendByZeroFun (E := E) (K := S) ((hf.restrict S).toLp f) : E → ℝ) =ᵐ[volume]
          (hf.toLp f : E → ℝ) := by
      have h1 := extendByZeroL2_ae_eq (E := E) (K := S) hS.measurableSet
        ((hf.restrict S).toLp f)
      have h2 :
          (extendByZeroL2 (E := E) (K := S) hS.measurableSet
            ((hf.restrict S).toLp f) : E → ℝ) =ᵐ[volume]
            (hf.toLp f : E → ℝ) := by rw [hExt]
      exact h1.symm.trans h2
    rw [smoothFun, hmul]
    exact MeasureTheory.convolution_congr (ContinuousLinearMap.mul ℝ ℝ)
      hzero EventuallyEq.rfl
  have hφsmooth (m : ℕ) : ContDiff ℝ ∞
      (smoothFun (E := E) (K := S) (ψ m) ((hφ0.restrict S).toLp φ)) := by
    rw [hconv φ hφ0 hsupp₀ m]
    exact contDiff_L2_convolution u₀ (hψ m).1 (hψ m).2.1
  have hφcompact (m : ℕ) : HasCompactSupport
      (smoothFun (E := E) (K := S) (ψ m) ((hφ0.restrict S).toLp φ)) :=
    hasCompactSupport_smoothFun (E := E) (K := S) (ψ m) hS
      (hψ m).2.1 ((hφ0.restrict S).toLp φ)
  have hsumK (m : ℕ) : S + tsupport (ψ m) ⊆ K := by
    intro z hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    have hyr : ‖y‖ < r m := by
      have := (hψ m).2.2.2.2 hy
      simpa [Metric.mem_ball, dist_eq_norm] using this
    have hry : r m < ε₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hxy : |(1 : ℝ)| * ‖y‖ < ε₀ := by simpa using hyr.trans hry
    exact interior_subset (by simpa using (hmargin y 1 hxy).1 x hx |>.1)
  have hφsupport (m : ℕ) : Function.support
      (smoothFun (E := E) (K := S) (ψ m) ((hφ0.restrict S).toLp φ)) ⊆ K :=
    (support_smoothFun_subset_add_tsupport (E := E) (K := S) (ψ := ψ m)
      ((hφ0.restrict S).toLp φ)).trans (hsumK m)
  let q₀ : ℕ → Lp ℝ 2 (volume : Measure E) := fun m =>
    smoothL2 (E := E) (K := S) (ψ m) hS hS.measurableSet (hψ m).1.continuous
      (hψ m).2.1 ((hφ0.restrict S).toLp φ)
  let q : ℕ → ι → Lp ℝ 2 (volume : Measure E) := fun m i =>
    smoothL2 (E := E) (K := S) (ψ m) hS hS.measurableSet (hψ m).1.continuous
      (hψ m).2.1 (((hφdi i).restrict S).toLp (d i))
  have hfd (m : ℕ) (i : ι) (x : E) :
      fderiv ℝ (smoothFun (E := E) (K := S) (ψ m)
        ((hφ0.restrict S).toLp φ)) x (b i) =
        ((du i : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (ψ m)) x := by
    rw [hconv φ hφ0 hsupp₀ m]
    exact fderiv_convolution_eq_weakDerivative_convolution u₀ (du i) (b i)
      (hweak i) (hψ m).1 (hψ m).2.1 x (subset_univ _)
  have hqderiv (m : ℕ) (i : ι) :
      q m i = (let hm := (hφsmooth m).continuous_fderiv (by norm_num)
        let hc := hφcompact m
        let hmem : MemLp (fun x => fderiv ℝ
          (smoothFun (E := E) (K := S) (ψ m)
            ((hφ0.restrict S).toLp φ)) x (b i)) 2 volume :=
          (hm.clm_apply continuous_const).memLp_of_hasCompactSupport
            (hc.fderiv_apply ℝ (b i))
        hmem.toLp (fun x => fderiv ℝ
          (smoothFun (E := E) (K := S) (ψ m)
            ((hφ0.restrict S).toLp φ)) x (b i))) := by
    let hm := (hφsmooth m).continuous_fderiv (by norm_num)
    let hc := hφcompact m
    let hmem : MemLp (fun x => fderiv ℝ
        (smoothFun (E := E) (K := S) (ψ m)
          ((hφ0.restrict S).toLp φ)) x (b i)) 2 volume :=
      (hm.clm_apply continuous_const).memLp_of_hasCompactSupport
        (hc.fderiv_apply ℝ (b i))
    apply MeasureTheory.Lp.ext
    have hqae := smoothL2_ae_eq (E := E) (K := S) (ψ := ψ m) hS hS.measurableSet
      (hψ m).1.continuous (hψ m).2.1 (((hφdi i).restrict S).toLp (d i))
    have hdiConv := hconv (d i) (hφdi i) (hsuppd i) m
    have hmemae := hmem.coeFn_toLp
    filter_upwards [hqae, hmemae] with x hqx hmx
    calc
      q m i x = smoothFun (E := E) (K := S) (ψ m)
          (((hφdi i).restrict S).toLp (d i)) x := hqx
      _ = ((du i : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
          (ψ m)) x := by rw [hdiConv]
      _ = fderiv ℝ (smoothFun (E := E) (K := S) (ψ m)
          ((hφ0.restrict S).toLp φ)) x (b i) := (hfd m i x).symm
      _ = hmem.toLp (fun x => fderiv ℝ (smoothFun (E := E) (K := S) (ψ m)
          ((hφ0.restrict S).toLp φ)) x (b i)) x := hmx.symm
  have hgraph (m : ℕ) :
      (q₀ m, fun i => q m i) ∈ smoothSupportedTestGraph (fun i => b i) K := by
    have hφtsupport : tsupport
        (smoothFun (E := E) (K := S) (ψ m) ((hφ0.restrict S).toLp φ)) ⊆ K :=
      closure_minimal (hφsupport m) hK.isClosed
    refine ⟨smoothFun (E := E) (K := S) (ψ m)
      ((hφ0.restrict S).toLp φ), hφsmooth m, hφcompact m, hφtsupport, ?_, ?_⟩
    · simpa [q₀] using smoothL2_ae_eq (E := E) (K := S) (ψ := ψ m) hS hS.measurableSet
        (hψ m).1.continuous (hψ m).2.1 ((hφ0.restrict S).toLp φ)
    · intro i
      change (q m i : E → ℝ) =ᵐ[(volume : Measure E)]
        (fun z => fderiv ℝ (smoothFun (E := E) (K := S) (ψ m)
          ((hφ0.restrict S).toLp φ)) z (b i))
      let hm := (hφsmooth m).continuous_fderiv (by norm_num)
      let hc := hφcompact m
      let hmem : MemLp (fun x => fderiv ℝ
          (smoothFun (E := E) (K := S) (ψ m)
            ((hφ0.restrict S).toLp φ)) x (b i)) 2 volume :=
        (hm.clm_apply continuous_const).memLp_of_hasCompactSupport
          (hc.fderiv_apply ℝ (b i))
      rw [hqderiv m i]
      exact hmem.coeFn_toLp
  have hq₀t : Tendsto q₀ atTop (𝓝 u₀) := by
    simpa [q₀, u₀] using awpj_smoothL2_kernel_tendsto hS φ hφ0 hsupp₀
      r hr hrt ψ (fun m => ⟨(hψ m).1.continuous, (hψ m).2.1,
        (hψ m).2.2.1, (hψ m).2.2.2.1, (hψ m).2.2.2.2⟩)
  have hqt : ∀ i, Tendsto (fun m => q m i) atTop (𝓝 (du i)) := by
    intro i
    simpa [q, du] using awpj_smoothL2_kernel_tendsto hS (d i) (hφdi i)
      (hsuppd i) r hr hrt ψ (fun m => ⟨(hψ m).1.continuous, (hψ m).2.1,
        (hψ m).2.2.1, (hψ m).2.2.2.1, (hψ m).2.2.2.2⟩)
  have hqfamily : Tendsto (fun m => fun i => q m i) atTop
      (𝓝 (fun i => du i)) := (tendsto_pi_nhds).2 hqt
  have hpt : Tendsto (fun m => (q₀ m, fun i => q m i)) atTop
      (𝓝 (u₀, fun i => du i)) := by
    simpa only [nhds_prod_eq] using hq₀t.prodMk hqfamily
  have hcl : (u₀, fun i => du i) ∈
      closure (smoothSupportedTestGraph (fun i => b i) K) := by
    apply isClosed_closure.mem_of_tendsto hpt
    exact Filter.Eventually.of_forall (fun m => subset_closure (hgraph m))
  convert hcl using 1 <;> simp [u₀, du, d]

/-! The approximation lemma is also the needed smooth-test extension.  The
equation is first interpreted as a continuous L² pairing, and only then is
the C¹ test recovered as a set integral. -/

theorem extend_weak_test_equation_to_c1
    {ι : Type uι} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {S K : Set E} (hS : IsCompact S) (hK : IsCompact K)
    (hSK : S ⊆ interior K) (P : ι → E → ℝ) (G : E → ℝ)
    (hP : ∀ j, MemLp (P j) 2 (volume.restrict K))
    (hG : MemLp G 2 (volume.restrict K))
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ K →
      (∑ j, ∫ z in K, P j z * fderiv ℝ φ z (b j)) =
        -(∫ z in K, G z * φ z)) :
    ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ S →
      (∑ j, ∫ z in S, P j z * fderiv ℝ φ z (b j)) =
        -(∫ z in S, G z * φ z) := by
  classical
  let Pg : ι → Lp ℝ 2 (volume : Measure E) := fun j =>
    Lp.extendByZeroₗᵢ hK.measurableSet ((hP j).toLp (P j))
  let Gg : Lp ℝ 2 (volume : Measure E) :=
    -(Lp.extendByZeroₗᵢ hK.measurableSet (hG.toLp G))
  have hPgae (j : ι) : (Pg j : E → ℝ) =ᵐ[volume]
      K.indicator (P j) := by
    have hp := (ae_restrict_iff' hK.measurableSet).mp (hP j).coeFn_toLp
    filter_upwards [Lp.extendByZeroₗᵢ_ae_eq hK.measurableSet
      ((hP j).toLp (P j)), hp] with z hz hpz
    exact hz.trans (by by_cases hzK : z ∈ K <;> simp [hzK, hpz])
  have hGgae : (Gg : E → ℝ) =ᵐ[volume]
      (fun z => -(K.indicator G z)) := by
    have hp := (ae_restrict_iff' hK.measurableSet).mp hG.coeFn_toLp
    filter_upwards [Lp.coeFn_neg (Lp.extendByZeroₗᵢ hK.measurableSet
      (hG.toLp G)), Lp.extendByZeroₗᵢ_ae_eq hK.measurableSet (hG.toLp G), hp]
      with z hn hz hpz
    exact hn.trans (by rw [Pi.neg_apply, hz]; by_cases hzK : z ∈ K <;>
      simp [hzK, hpz])
  have hgraph_eq : ∀ p ∈ smoothSupportedTestGraph (fun i => b i) K,
      (∑ j, inner ℝ (Pg j) (p.2 j)) = inner ℝ Gg p.1 := by
    intro p hp
    obtain ⟨θ, hθ, hcθ, hsθ, hpθ, hpdθ⟩ := hp
    have hl (j : ι) : inner ℝ (Pg j) (p.2 j) =
        ∫ z in K, P j z * fderiv ℝ θ z (b j) := by
      rw [L2.inner_def]
      calc
        _ = ∫ z, K.indicator (fun z => P j z * fderiv ℝ θ z (b j)) z := by
          apply integral_congr_ae
          filter_upwards [hPgae j, hpdθ j] with z hz hd
          simp only [RCLike.inner_apply, conj_trivial, hz, hd]
          by_cases hzK : z ∈ K <;> simp [hzK, mul_comm]
        _ = _ := integral_indicator hK.measurableSet
    have hr : inner ℝ Gg p.1 = -(∫ z in K, G z * θ z) := by
      rw [L2.inner_def, ← integral_indicator hK.measurableSet, ← integral_neg]
      apply integral_congr_ae
      filter_upwards [hGgae, hpθ] with z hz hθz
      simp only [RCLike.inner_apply, conj_trivial, hz, hθz]
      by_cases hzK : z ∈ K <;> simp [hzK, mul_comm]
    simp_rw [hl]
    rw [hr]
    exact h θ hθ hcθ hsθ
  have hclosed : IsClosed {p : Lp ℝ 2 (volume : Measure E) ×
      (ι → Lp ℝ 2 (volume : Measure E)) |
      (∑ j, inner ℝ (Pg j) (p.2 j)) = inner ℝ Gg p.1} := by
    apply isClosed_eq
    · exact continuous_finsetSum _ fun j _ =>
        continuous_const.inner ((continuous_apply j).comp continuous_snd)
    · exact continuous_const.inner continuous_fst
  intro φ hφ hcφ hsφ
  have hφ0 : MemLp φ 2 (volume : Measure E) :=
    hφ.continuous.memLp_of_hasCompactSupport hcφ
  have hφd (j : ι) : MemLp (fun z => fderiv ℝ φ z (b j)) 2
      (volume : Measure E) :=
    ((hφ.continuous_fderiv (by norm_num)).clm_apply
      (continuous_const (y := b j))).memLp_of_hasCompactSupport
        (hcφ.fderiv_apply ℝ (b j))
  have hpcl := c1SupportedTestGraph_mem_closure_smoothSupportedTestGraph
    b hS hK hSK hφ hcφ hsφ
  have hsubset : closure (smoothSupportedTestGraph (fun i => b i) K) ⊆
      {p : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E)) |
        (∑ j, inner ℝ (Pg j) (p.2 j)) = inner ℝ Gg p.1} :=
    closure_minimal hgraph_eq hclosed
  have heq := hsubset hpcl
  have hl (j : ι) : inner ℝ (Pg j)
      (((hφd j).toLp (fun z => fderiv ℝ φ z (b j)))) =
        ∫ z in K, P j z * fderiv ℝ φ z (b j) := by
    rw [L2.inner_def]
    calc
      _ = ∫ z, K.indicator (fun z => P j z * fderiv ℝ φ z (b j)) z := by
        apply integral_congr_ae
        filter_upwards [hPgae j, (hφd j).coeFn_toLp] with z hz hd
        simp only [RCLike.inner_apply, conj_trivial, hz, hd]
        by_cases hzK : z ∈ K <;> simp [hzK, mul_comm]
      _ = _ := integral_indicator hK.measurableSet
  have hr : inner ℝ Gg (hφ0.toLp φ) = -(∫ z in K, G z * φ z) := by
    rw [L2.inner_def, ← integral_indicator hK.measurableSet, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [hGgae, hφ0.coeFn_toLp] with z hz hφz
    simp only [RCLike.inner_apply, conj_trivial, hz, hφz]
    by_cases hzK : z ∈ K <;> simp [hzK, mul_comm]
  have hK_eq : (∑ j, ∫ z in K, P j z * fderiv ℝ φ z (b j)) =
      -(∫ z in K, G z * φ z) := by
    change (∑ j, inner ℝ (Pg j)
        (((hφd j).toLp (fun z => fderiv ℝ φ z (b j)))) ) =
      inner ℝ Gg (hφ0.toLp φ) at heq
    rw [← hr]
    simpa only [hl] using heq
  have hzero (z : E) (hz : z ∉ S) :
      φ z = 0 ∧ fderiv ℝ φ z = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport (fun hh => hz (hsφ hh)),
      fderiv_of_notMem_tsupport ℝ (fun hh => hz (hsφ hh))⟩
  have hleft (j : ι) :
      (∫ z in K, P j z * fderiv ℝ φ z (b j)) =
        ∫ z in S, P j z * fderiv ℝ φ z (b j) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
      (fun z hzK => by
        have hzS : z ∉ S := fun hz => hzK (interior_subset (hSK hz))
        simp [(hzero z hzS).2]),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
      (fun z hzS => by simp [(hzero z hzS).2])]
  have hright : (∫ z in K, G z * φ z) = ∫ z in S, G z * φ z := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
      (fun z hzK => by
        have hzS : z ∉ S := fun hz => hzK (interior_subset (hSK hz))
        simp [(hzero z hzS).1]),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
      (fun z hzS => by simp [(hzero z hzS).1])]
  calc
    (∑ j, ∫ z in S, P j z * fderiv ℝ φ z (b j)) =
        ∑ j, ∫ z in K, P j z * fderiv ℝ φ z (b j) := by
      exact (Finset.sum_congr rfl (fun j _ => hleft j)).symm
    _ = -(∫ z in K, G z * φ z) := hK_eq
    _ = -(∫ z in S, G z * φ z) := by rw [hright]

/-! A scalar weak identity is the one-coordinate special case of the same
extension argument.  Keeping this as a wrapper avoids introducing a second
density proof for the derivative identities used by the induction. -/

theorem extend_weak_directional_derivative_to_c1
    {ι : Type uι} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (i : ι)
    {S K : Set E} (hS : IsCompact S) (hK : IsCompact K)
    (hSK : S ⊆ interior K) (U d : E → ℝ)
    (hU : MemLp U 2 (volume.restrict K))
    (hd : MemLp d 2 (volume.restrict K))
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ K →
      (∫ z in K, U z * fderiv ℝ φ z (b i)) =
        -(∫ z in K, d z * φ z)) :
    ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ S →
      (∫ z in S, U z * fderiv ℝ φ z (b i)) =
        -(∫ z in S, d z * φ z) := by
  classical
  let P : ι → E → ℝ := fun j => if j = i then U else 0
  have hP (j : ι) : MemLp (P j) 2 (volume.restrict K) := by
    by_cases hji : j = i
    · subst j
      simp [P, hU]
    · simpa [P, hji] using
        (memLp_zero : MemLp (fun _ : E => (0 : ℝ)) 2 (volume.restrict K))
  have hPDE : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ K →
      (∑ j, ∫ z in K, P j z * fderiv ℝ φ z (b j)) =
        -(∫ z in K, d z * φ z) := by
    intro φ hφ hc hs
    have he := h φ hφ hc hs
    dsimp [P]
    rw [Finset.sum_eq_single i]
    · simpa using he
    · intro j hj hji
      simp [hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have he := extend_weak_test_equation_to_c1 b hS hK hSK P d hP hd hPDE
  intro φ hφ hc hs
  have hh := he φ hφ hc hs
  dsimp [P] at hh
  rw [Finset.sum_eq_single i] at hh
  · simpa using hh
  · intro j hj hji
    simp [hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-! ## Coefficient quotients from smoothness alone -/

theorem exists_matrix_quotient_bound
    {ι : Type uι} [Fintype ι]
    {A : E → Matrix ι ι ℝ} {K W : Set E}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hconv : Convex ℝ K) (hA : ContDiffOn ℝ ∞ A W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x v : E) (h : ℝ), h ≠ 0 → x ∈ K →
      x + h • v ∈ K →
      ‖h⁻¹ • (A (x + h • v) - A x)‖ ≤ C * ‖v‖ := by
  classical
  have hentry (i j : ι) : ContDiffOn ℝ ∞ (fun z => A z i j) W := by
    exact contDiffOn_pi.mp (contDiffOn_pi.mp hA i) j
  have hb (i j : ι) : ∃ C : ℝ, ∀ z ∈ K,
      ‖fderiv ℝ (fun y => A y i j) z‖ ≤ C := by
    have hc := (hentry i j).continuousOn_fderiv_of_isOpen hW (by norm_num)
    exact hK.exists_bound_of_continuousOn (hc.mono hKW)
  choose C hC using hb
  let B : ℝ := ∑ i, ∑ j, max (C i j) 0
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro x v h hh hx hy
  apply (Matrix.norm_le_iff (mul_nonneg hB (norm_nonneg v))).mpr
  intro i j
  have hd := hentry i j
  have hscalar := hconv.norm_image_sub_le_of_norm_fderiv_le
    (C := max (C i j) 0)
    (fun z hz => (hd.contDiffAt (hW.mem_nhds (hKW hz))).differentiableAt
      (by norm_num))
    (fun z hz => (hC i j z hz).trans (le_max_left _ _)) hx hy
  have hscalar' : ‖h⁻¹ * (A (x + h • v) i j - A x i j)‖ ≤ B * ‖v‖ := by
    rw [add_sub_cancel_left, norm_smul] at hscalar
    rw [norm_mul]
    calc
      _ ≤ ‖h⁻¹‖ * (max (C i j) 0 * (‖h‖ * ‖v‖)) :=
        mul_le_mul_of_nonneg_left hscalar (norm_nonneg _)
      _ = max (C i j) 0 * ‖v‖ := by
        rw [norm_inv]
        field_simp
      _ ≤ (∑ j, max (C i j) 0) * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun j _ => le_max_right _ _)
            (Finset.mem_univ j)) (norm_nonneg _)
      _ ≤ B * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right
          (Finset.single_le_sum
            (fun i _ => Finset.sum_nonneg fun j _ => le_max_right _ _)
            (Finset.mem_univ i)) (norm_nonneg _)
  simpa [Matrix.smul_apply, sub_apply, smul_eq_mul, norm_mul] using hscalar'

/-! A tail of an existing jet is the first-order jet needed to represent the
equation at that tail.  The append order agrees with the convention that a
weak derivative is prepended to a word. -/

def shiftedLocalJet
    {ι : Type uι} {b : ι → E} {K T : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) (hTK : T ⊆ K)
    (w : List ι) (hw : w.length < n) :
    LocalL2DerivativeJet b T 1 :=
  ⟨fun v => J.value (v ++ w), by
    intro v hv i
    cases v with
    | nil =>
        simpa using (J.weak w (by omega) i).restrict hTK
    | cons a t =>
        simp only [List.length_cons] at hv
        omega⟩

/-! A small cross-order reindexer.  The successor jet has one more weak
derivative than its predecessor, so the already available same-order
reindexing lemma is not applicable to the forcing expressions at the
interface. -/

namespace WeakExpr

variable {ι : Type uι} [Fintype ι]
  {K₁ K₂ : Set E} {n₁ n₂ : ℕ} {b : ι → E}
  {J₁ : LocalL2DerivativeJet b K₁ n₁}
  {J₂ : LocalL2DerivativeJet b K₂ n₂}
  {A : E → ι → ι → ℝ} {F : E → ℝ}

def reindexCross (p : WeakExpr b J₁ A F) : WeakExpr b J₂ A F :=
  match p with
  | .zero => .zero
  | .smoothF w => .smoothF w
  | .coeff i j w => .coeff i j w
  | .jet w => .jet w
  | .add p q => .add (reindexCross p) (reindexCross q)
  | .sub p q => .sub (reindexCross p) (reindexCross q)
  | .coeffMul i j w p => .coeffMul i j w (reindexCross p)
  | .sum p => .sum (fun i => reindexCross (p i))

theorem eval_reindexCross_eq_of_bound
    (p : WeakExpr b J₁ A F)
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

theorem reindexCross_deriv (k : ι) (p : WeakExpr b J₁ A F) :
    reindexCross (J₂ := J₂) (deriv k p) =
      deriv k (reindexCross (J₂ := J₂) p) := by
  induction p with
  | zero | smoothF _ | coeff _ _ _ | jet _ => rfl
  | add p q hp hq => simp [deriv, reindexCross, hp, hq]
  | sub p q hp hq => simp [deriv, reindexCross, hp, hq]
  | coeffMul i j w p hp => simp [deriv, reindexCross, hp]
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

end WeakExpr

/-! ## One elliptic bootstrap step -/

theorem exists_weak_poisson_jet_successor
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
    (hJ : WeakPoissonHierarchy J A F) (hn : 2 ≤ n) :
    ∃ J' : LocalL2DerivativeJet (fun i => b i) S (n + 1),
      WeakPoissonHierarchy J' A F ∧
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
            (WeakExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F)
              (k :: w)).eval z * φ z) := by
    intro φ hφ hcφ hsφ
    let p₀ := WeakExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F) w
    have hp₀ : p₀.jetBound + 1 ≤ n := by
      have hbound := WeakExpr.jetBound_forcing_le (b := fun i => b i)
        (J := J) (A := A) (F := F) w
      dsimp [p₀]
      omega
    have hwp₀ := WeakExpr.weak_derivative_eval hK hW hKW hAij hF p₀ hp₀ k
    have hdF₀ : MemLp (WeakExpr.deriv k p₀).eval 2 (volume.restrict K) := by
      apply WeakExpr.memLp_eval hK hW hKW hAij hF
      exact (WeakExpr.jetBound_deriv_le k p₀).trans hp₀
    obtain ⟨hGmem, hGeq⟩ := J.exists_scalar_forcing_differentiated_equation_of_weak_forcing
      w hw hK hW hKW k A p₀.eval (WeakExpr.deriv k p₀).eval hAij hdF₀ hwp₀ (hJ w hw)
    let G : E → ℝ := fun z =>
      (WeakExpr.deriv k p₀).eval z - ∑ j, ∑ i,
        (fderiv ℝ (fun y => fderiv ℝ (fun x => A x i j) y (b k)) z (b j) *
            J.value (i :: w) z +
          fderiv ℝ (fun y => A y i j) z (b k) * J.value (j :: i :: w) z)
    have hGmem' : MemLp G 2 (volume.restrict K) := by
      simpa [G] using hGmem
    have hGforcing : G =
        (WeakExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F)
          (k :: w)).eval := by
      simpa [G, p₀] using
        (WeakExpr.forcing_cons_eval (b := fun i => b i) (J := J) (A := A)
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
          (WeakExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F)
            (k :: w)).eval z * φ z) := by rw [hGforcing]

  have htailEquation (w : List ι) (hw : w.length + 1 = n) :
      ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
        tsupport φ ⊆ T →
        (∑ j, ∫ z in T, (∑ i, A z i j * J.value (i :: w) z) *
          fderiv ℝ φ z (b j)) =
          -(∫ z in T,
            (WeakExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F)
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
        (WeakExpr.forcing (b := fun j => b j) (J := J) (A := A) (F := F) tail).eval
        2 (volume.restrict T) := by
      have hjet : (WeakExpr.forcing (b := fun j => b j) (J := J)
          (A := A) (F := F) tail).jetBound ≤ n := by
        exact (WeakExpr.jetBound_forcing_le (b := fun j => b j)
          (J := J) (A := A) (F := F) tail).trans (by omega)
      have hFtailK : MemLp
          (WeakExpr.forcing (b := fun j => b j) (J := J) (A := A) (F := F) tail).eval
          2 (volume.restrict K) := by
        exact WeakExpr.memLp_eval (J := J) (A := fun z i j => A z i j) (F := F)
          hK hW hKW hAij hF
          (WeakExpr.forcing (b := fun j => b j) (J := J) (A := A) (F := F) tail)
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
        (WeakExpr.forcing (b := fun j => b j) (J := J) (A := A) (F := F) tail).eval
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
                (WeakExpr.forcing (b := fun j => b j) (J := J) (A := A)
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
        (WeakExpr.forcing (b := fun i => b i) (J := J') (A := A) (F := F) w).eval) :
      weakCoefficientEquation A J' w
        (WeakExpr.forcing (b := fun i => b i) (J := J') (A := A) (F := F) w).eval := by
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
          (WeakExpr.forcing (b := fun i => b i) (J := J') (A := A) (F := F) w).eval z * φ z) := by
        rw [hforcing]
  refine ⟨J', ?_, ?_⟩
  intro w hw
  have hwle : w.length + 1 ≤ n := by omega
  by_cases hlow : w.length + 1 < n
  · have hbase := weakCoefficientEquation.restrict (hJ w hlow) hSKK
    have h₀ : weakCoefficientEquation A JS w
        (WeakExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F) w).eval := by
      simpa [JS] using hbase
    have hforcing := WeakExpr.eval_forcing_cross_eq_of_bound
      (J₁ := J) (J₂ := J') (A := fun z i j => A z i j) (F := F) w
      hJtoJ' hwle
    apply htransport w
      (WeakExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F) w).eval
      JS h₀
    · intro i
      exact (hpres (i :: w) (by simp only [List.length_cons]; omega)).symm
    · exact hforcing
  · have hwEq : w.length + 1 = n := by omega
    have hSTT : S ⊆ T := hST.trans interior_subset
    let JT : LocalL2DerivativeJet (fun i => b i) T n := J.restrict hTKK
    have hT₀ : weakCoefficientEquation A JT w
        (WeakExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F) w).eval := by
      intro θ hθ hcθ hsθ
      exact htailEquation w hwEq θ (hθ.of_le (by norm_num)) hcθ hsθ
    have hS₀ := weakCoefficientEquation.restrict hT₀ hSTT
    let JTS : LocalL2DerivativeJet (fun i => b i) S n := JT.restrict hSTT
    have h₀ : weakCoefficientEquation A JTS w
        (WeakExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F) w).eval := by
      simpa [JTS] using hS₀
    have hforcing := WeakExpr.eval_forcing_cross_eq_of_bound
      (J₁ := J) (J₂ := J') (A := fun z i j => A z i j) (F := F) w
      hJtoJ' hwle
    apply htransport w
      (WeakExpr.forcing (b := fun i => b i) (J := J) (A := A) (F := F) w).eval
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
theorem exists_weak_poisson_jets_on_nested_compacts
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
    (hJ₂ : WeakPoissonHierarchy J₂ A F) :
    ∀ n : ℕ, ∃ J : LocalL2DerivativeJet (fun i => b i) S n,
      WeakPoissonHierarchy J A F ∧
        ∀ w : List ι, w.length ≤ 2 → J.value w = J₂.value w := by
  have hKsub0 : ∀ m, K m ⊆ K 0 := by
    intro m
    induction m with
    | zero => exact subset_rfl
    | succ m ih =>
        exact (hstep m).trans (interior_subset.trans ih)
  have hchain : ∀ m, ∃ Jm : LocalL2DerivativeJet (fun i => b i) (K m) (m + 2),
      WeakPoissonHierarchy Jm A F ∧
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
        obtain ⟨Jnext, hJnext, hnext⟩ := exists_weak_poisson_jet_successor b
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
    have hJn : WeakPoissonHierarchy Jn A F := hJm.restrict hSm
    subst n
    exact ⟨Jn, hJn, fun w hw => hbase w hw⟩
  · let Jsmall : LocalL2DerivativeJet (fun i => b i) S n :=
      (J₂.restrict hS0).truncate (by omega)
    refine ⟨Jsmall, ?_, ?_⟩
    unfold WeakPoissonHierarchy
    intro w hw
    omega
    intro w hw
    rfl

/-! A base equation is exactly the order-two instance of the hierarchy. -/

theorem weakPoissonHierarchy_of_order_two_equation
    {ι : Type uι} [Fintype ι]
    {b : ι → E} {K : Set E}
    {A : E → Matrix ι ι ℝ} {F : E → ℝ}
    (J : LocalL2DerivativeJet b K 2)
    (hbase : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (∑ i, A z i j * J.value (i :: []) z) *
        fderiv ℝ φ z (b j)) = -(∫ z in K, F z * φ z)) :
    WeakPoissonHierarchy J A F := by
  intro w hw
  have hw0 : w.length = 0 := by omega
  have hw_nil : w = [] := List.eq_nil_of_length_eq_zero hw0
  subst w
  simpa [weakCoefficientEquation, WeakExpr.forcing, WeakExpr.eval,
    localDirectionalIterate] using hbase

/-! ## The actual weak Poisson solution, with no quotient hypothesis -/

open Bundle

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local instance awpjActualMetric0 :
    IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)

local instance awpjActualContinuousMetric :
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- The arbitrary-order construction applied to the actual weak Poisson
solution.  The forcing is assumed smooth on the chart, which is the precise
regularity needed to differentiate it at every finite order; no derivative
bound for any jet field is assumed. -/
theorem exists_weakPoisson_all_order_jets_on_nested_compacts
    (b : OrthonormalBasis ι ℝ E) (c : M)
    {Kbig : Set E} {K : ℕ → Set E} {S : Set E}
    (hKbig : IsCompact Kbig)
    (hKbig_target : Kbig ⊆ (extChartAt I c).target)
    (hconvbig : Convex ℝ Kbig)
    (hK0big : K 0 ⊆ interior Kbig)
    (hK : ∀ m, IsCompact (K m))
    (hconv : ∀ m, Convex ℝ (K m))
    (hstep : ∀ m, K (m + 1) ⊆ interior (K m))
    (hS : IsCompact S)
    (hSall : ∀ m, S ⊆ interior (K m))
    (f : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hf : (∫ x, f x ∂riemannianVolume (I := I)) = 0)
    (F : E → ℝ)
    (hF : ContDiffOn ℝ ∞ F (extChartAt I c).target)
    (hFae : F =ᵐ[volume.restrict Kbig]
      (fun z => matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
        f ((extChartAt I c).symm z))) :
    ∃ v : Lp ℝ 2 (volume : Measure E),
      ∀ n : ℕ, ∃ J : LocalL2DerivativeJet (fun i => b i) S n,
        WeakPoissonHierarchy J
            (coordinateEllipticMatrix (I := I) b.toBasis c)
            F ∧ J.value [] = v ∧
          (J.value [] : E → ℝ) =ᵐ[volume.restrict S]
            (fun z => energyCompletionToL2 (weakPoissonSolution f)
              ((extChartAt I c).symm z)) := by
  let A : E → Matrix ι ι ℝ := coordinateEllipticMatrix (I := I) b.toBasis c
  let Fraw : E → ℝ := fun z =>
    matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
      f ((extChartAt I c).symm z)
  have hA : ContDiffOn ℝ ∞ A (extChartAt I c).target := by
    simpa [A] using
      (contDiffOn_coordinateEllipticMatrix_of_order (I := I) ∞ b.toBasis c)
  have hK0big' : K 0 ⊆ Kbig := hK0big.trans interior_subset
  have hK0target : K 0 ⊆ (extChartAt I c).target :=
    hK0big.trans (interior_subset.trans hKbig_target)
  obtain ⟨ell, hell, hEllbig⟩ :=
    exists_coordinateEllipticMatrix_lower_bound b.toBasis c hKbig hKbig_target
  have hEll : ∀ x ∈ K 0, ∀ u : EuclideanSpace ℝ ι,
      ell * ‖u‖ ^ 2 ≤ ∑ i, ∑ j, A x i j * u i * u j := by
    intro x hx u
    simpa [A] using hEllbig x (hK0big' hx) u
  have hAc : ContinuousOn A Kbig := by
    simpa [A] using
      (continuousOn_coordinateEllipticMatrix (I := I) b.toBasis c).mono
        hKbig_target
  obtain ⟨Lam, hLam, hbilbig⟩ := exists_uniform_matrix_bilinear_bound hKbig A hAc
  have hbil : ∀ x ∈ K 0, ∀ u w : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, A x i j * u i * w j| ≤ Lam * ‖u‖ * ‖w‖ := by
    intro x hx u w
    exact hbilbig x (hK0big' hx) u w
  obtain ⟨J₂, _, _, hJ₂root, hJ₂one, _, _⟩ :=
    exists_weakPoisson_local_L2_jet_two_symmetric b c hKbig hKbig_target hconvbig
      (hK 0) hK0big f hf
  have hAij (i j : ι) : ContDiffOn ℝ ∞ (fun z => A z i j)
      (extChartAt I c).target := by
    exact contDiffOn_pi.mp (contDiffOn_pi.mp hA i) j
  have hbase : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ K 0 →
      (∑ j, ∫ z in K 0, (∑ i, A z i j * J₂.value (i :: []) z) *
        fderiv ℝ φ z (b j)) = -(∫ z in K 0, F z * φ z) := by
    intro φ hφ hcφ hsφ
    have hdata := (weakPoissonSolution_local_data b c hKbig hKbig_target f hf).variational
      φ (hφ.of_le (by norm_num)) hcφ (hsφ.trans hK0big')
    have hflux (j : ι) : Integrable
        (fun z => (∑ i, A z i j * J₂.value (i :: []) z) *
          fderiv ℝ φ z (b j)) (volume.restrict (K 0)) := by
      have hAj : MemLp (fun z => ∑ i, A z i j * J₂.value (i :: []) z) 2
          (volume.restrict (K 0)) := by
        apply memLp_finsetSum
        intro i hi
        exact memLp_mul_coefficient_on_compact (hK 0)
          ((hAij i j).continuousOn.mono hK0target)
          ((Lp.memLp (J₂.value [i])).restrict (K 0))
      have hφj : MemLp (fun z => fderiv ℝ φ z (b j)) 2
          (volume.restrict (K 0)) :=
        (((hφ.continuous_fderiv (by norm_num)).clm_apply
          (continuous_const (y := b j))).memLp_of_hasCompactSupport
          (hcφ.fderiv_apply ℝ (b j))).restrict (K 0)
      exact hAj.integrable_mul hφj
    have hzeroL (z : E) (hz : z ∉ K 0) :
        ∑ i, ∑ j, A z i j *
          energyChartDerivative c hKbig hKbig_target (b i)
            (weakPoissonSolution f) z * fderiv ℝ φ z (b j) = 0 := by
      have hdz : fderiv ℝ φ z = 0 :=
        fderiv_of_notMem_tsupport ℝ (fun hh => hz (hsφ hh))
      simp [hdz]
    have hzeroLbig (z : E) (hz : z ∉ Kbig) :
        ∑ i, ∑ j, A z i j *
          energyChartDerivative c hKbig hKbig_target (b i)
            (weakPoissonSolution f) z * fderiv ℝ φ z (b j) = 0 :=
      hzeroL z (fun hz0 => hz (hK0big' hz0))
    have hzeroR (z : E) (hz : z ∉ K 0) : F z * φ z = 0 := by
      simp [image_eq_zero_of_notMem_tsupport (fun hh => hz (hsφ hh))]
    have hzeroRbig (z : E) (hz : z ∉ Kbig) : F z * φ z = 0 :=
      hzeroR z (fun hz0 => hz (hK0big' hz0))
    have hdata0 :
        (∫ z in K 0, ∑ i, ∑ j, A z i j *
          energyChartDerivative c hKbig hKbig_target (b i)
            (weakPoissonSolution f) z * fderiv ℝ φ z (b j)) =
          -(∫ z in K 0, F z * φ z) := by
      calc
        (∫ z in K 0, ∑ i, ∑ j, A z i j *
            energyChartDerivative c hKbig hKbig_target (b i)
              (weakPoissonSolution f) z * fderiv ℝ φ z (b j)) =
            ∫ z, ∑ i, ∑ j, A z i j *
              energyChartDerivative c hKbig hKbig_target (b i)
                (weakPoissonSolution f) z * fderiv ℝ φ z (b j) :=
          setIntegral_eq_integral_of_forall_compl_eq_zero hzeroL
        _ = ∫ z in Kbig, ∑ i, ∑ j, A z i j *
              energyChartDerivative c hKbig hKbig_target (b i)
                (weakPoissonSolution f) z * fderiv ℝ φ z (b j) :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hzeroLbig).symm
        _ = -(∫ z in Kbig, Fraw z * φ z) := hdata
        _ = -(∫ z in Kbig, F z * φ z) := by
          congr 1
          exact integral_congr_ae (hFae.mul EventuallyEq.rfl).symm
        _ = -(∫ z, F z * φ z) := by
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroRbig]
        _ = -(∫ z in K 0, F z * φ z) := by
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroR]
    calc
      (∑ j, ∫ z in K 0, (∑ i, A z i j * J₂.value (i :: []) z) *
          fderiv ℝ φ z (b j)) =
          ∫ z in K 0, ∑ j, (∑ i, A z i j * J₂.value (i :: []) z) *
            fderiv ℝ φ z (b j) := by
        rw [integral_finsetSum]
        intro j hj
        exact hflux j
      _ = ∫ z in K 0, ∑ i, ∑ j,
          A z i j * J₂.value (i :: []) z * fderiv ℝ φ z (b j) := by
        congr 1
        funext z
        simp_rw [Finset.sum_mul]
        exact Finset.sum_comm
      _ = ∫ z in K 0, ∑ i, ∑ j,
          A z i j * energyChartDerivative c hKbig hKbig_target (b i)
            (weakPoissonSolution f) z * fderiv ℝ φ z (b j) := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hJ₂one] with z hz
        apply Finset.sum_congr rfl
        intro i hi
        simp_rw [hz i]
      _ = -(∫ z in K 0, F z * φ z) := by
        exact hdata0
  have hJ₂hier : WeakPoissonHierarchy J₂ A F :=
    weakPoissonHierarchy_of_order_two_equation J₂ hbase
  have hall := exists_weak_poisson_jets_on_nested_compacts
    (E := E) b (K := K) (S := S) (W := (extChartAt I c).target)
    hK hconv hstep hS hSall (isOpen_extChartAt_target c) hK0target
    A F hA hF hell hLam hEll hbil J₂ hJ₂hier
  have hS0 : S ⊆ K 0 := (hSall 0).trans interior_subset
  have hm : (volume : Measure E).restrict S ≤ volume.restrict (K 0) :=
    Measure.restrict_mono_set _ hS0
  refine ⟨J₂.value [], ?_⟩
  intro n
  obtain ⟨J, hJ, hpres⟩ := hall n
  refine ⟨J, hJ, hpres [] (by simp), ?_⟩
  have hpres0 : (J.value [] : E → ℝ) =ᵐ[volume.restrict S]
      (J₂.value [] : E → ℝ) := by
    have heq : (J.value [] : E → ℝ) = (J₂.value [] : E → ℝ) :=
      congrArg (fun q : Lp ℝ 2 (volume : Measure E) => (q : E → ℝ))
        (hpres [] (by simp))
    filter_upwards [] with z
    exact congrFun heq z
  exact hpres0.trans (hJ₂root.filter_mono (ae_mono hm))

end AlmostSchur
