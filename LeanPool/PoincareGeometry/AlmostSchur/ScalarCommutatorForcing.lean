/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.PostH2Bootstrap

/-! # Eliminating divergence commutators using genuine weak derivatives

The differentiated principal equation has scalar L² forcing once the
commutator flux has the weak derivatives supplied by the previous jet level.
This is an equation conversion, not a derivative-gain theorem.
-/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem weak_divergence_remove_commutator
    {ι : Type*} [Fintype ι] (b : ι → E) (K : Set E)
    (P C dC : ι → E → ℝ) (F : E → ℝ)
    (hP : ∀ j, MemLp (P j) 2 (volume.restrict K))
    (hC : ∀ j, MemLp (C j) 2 (volume.restrict K))
    (hdC : ∀ j, MemLp (dC j) 2 (volume.restrict K))
    (hF : MemLp F 2 (volume.restrict K))
    (hweak : ∀ j, HasWeakDirectionalDerivativeOn K (b j) (C j) (dC j))
    (hPDE : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (P j z + C j z) * fderiv ℝ φ z (b j)) =
        -(∫ z in K, F z * φ z)) :
    MemLp (fun z => F z - ∑ j, dC j z) 2 (volume.restrict K) ∧
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, P j z * fderiv ℝ φ z (b j)) =
        -(∫ z in K, (F z - ∑ j, dC j z) * φ z) := by
  refine ⟨hF.sub (memLp_finsetSum _ (fun j _ => hdC j)), ?_⟩
  intro φ hφ hc hs
  have ht : MemLp φ 2 (volume.restrict K) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc : MemLp φ 2 volume).restrict K
  have hdt (j : ι) : MemLp (fun z => fderiv ℝ φ z (b j)) 2 (volume.restrict K) :=
    ((contDiff_smooth_test_derivative hφ (b j)).continuous.memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ (b j)) : MemLp _ 2 volume).restrict K
  have he := hPDE φ hφ hc hs
  have hex (j : ι) : (∫ z in K, (P j z + C j z) * fderiv ℝ φ z (b j)) =
      (∫ z in K, P j z * fderiv ℝ φ z (b j)) - ∫ z in K, dC j z * φ z := by
    simp_rw [add_mul]
    rw [integral_add (f := fun z => P j z * fderiv ℝ φ z (b j))
      (g := fun z => C j z * fderiv ℝ φ z (b j)) ((hP j).integrable_mul (hdt j))
      ((hC j).integrable_mul (hdt j)), hweak j φ hφ hc hs, sub_eq_add_neg]
  simp_rw [hex, Finset.sum_sub_distrib] at he
  have hr : (∫ z in K, (F z - ∑ j, dC j z) * φ z) =
      (∫ z in K, F z * φ z) - ∑ j, ∫ z in K, dC j z * φ z := by
    simp_rw [sub_mul, Finset.sum_mul]
    rw [integral_sub (f := fun z => F z * φ z)
      (g := fun z => ∑ j, dC j z * φ z) (hF.integrable_mul ht)
      (integrable_finsetSum Finset.univ (fun j _ => (hdC j).integrable_mul ht)),
      integral_finsetSum (f := fun j z => dC j z * φ z)
        Finset.univ (fun j _ => (hdC j).integrable_mul ht)]
  rw [hr]
  linarith

/-- At any valid jet level, the coefficient commutator has an explicit L²
weak divergence involving only the already available jet levels. -/
theorem LocalL2DerivativeJet.commutator_weak_derivative
    {ι : Type*} [Fintype ι] {b : ι → E} {K W : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) (w : List ι) (hw : w.length + 1 < n)
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (k j : ι) (A : E → ι → ι → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) W) :
    let C := fun z => ∑ i, fderiv ℝ (fun y => A y i j) z (b k) * J.value (i :: w) z
    let dC := fun z => ∑ i,
      (fderiv ℝ (fun y => fderiv ℝ (fun x => A x i j) y (b k)) z (b j) *
        J.value (i :: w) z +
       fderiv ℝ (fun y => A y i j) z (b k) * J.value (j :: i :: w) z)
    MemLp C 2 (volume.restrict K) ∧ MemLp dC 2 (volume.restrict K) ∧
      HasWeakDirectionalDerivativeOn K (b j) C dC := by
  dsimp only
  have ha (i : ι) : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ (fun y => A y i j) z (b k)) W :=
    ((hA i j).fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const
  have hda (i : ι) : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ (fun y => fderiv ℝ (fun x => A x i j) y (b k)) z (b j)) W :=
    ((ha i).fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const
  have hu (i : ι) := (Lp.memLp (J.value (i :: w))).restrict K
  have hdu (i : ι) := (Lp.memLp (J.value (j :: i :: w))).restrict K
  have hm (i : ι) := memLp_mul_coefficient_on_compact hK
    ((ha i).continuousOn.mono hKW) (hu i)
  have hdm (i : ι) := (memLp_mul_coefficient_on_compact hK
    ((hda i).continuousOn.mono hKW) (hu i)).add
    (memLp_mul_coefficient_on_compact hK ((ha i).continuousOn.mono hKW) (hdu i))
  refine ⟨memLp_finsetSum _ (fun i _ => hm i),
    memLp_finsetSum _ (fun i _ => hdm i), ?_⟩
  exact HasWeakDirectionalDerivativeOn.finset_sum Finset.univ _ _
    (fun i _ => hm i) (fun i _ => hdm i) (fun i _ =>
      (J.weak (i :: w) (by simpa using hw) j).mul_coefficient hW hKW
        (hu i) (hdu i) (ha i))

/-- Differentiating a jet equation yields a principal divergence equation
with genuine scalar L² forcing, without a classical derivative of the jet. -/
theorem LocalL2DerivativeJet.exists_scalar_forcing_differentiated_equation
    {ι : Type*} [Fintype ι] {b : ι → E} {K W : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) (w : List ι) (hw : w.length + 1 < n)
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (k : ι) (A : E → ι → ι → ℝ) (F : E → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) W)
    (hF : ContDiffOn ℝ ∞ F W)
    (hPDE : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (∑ i, A z i j * J.value (i :: w) z) *
        fderiv ℝ φ z (b j)) = -(∫ z in K, F z * φ z)) :
    ∃ G : E → ℝ, MemLp G 2 (volume.restrict K) ∧
      (∀ z, G z = fderiv ℝ F z (b k) - ∑ j, ∑ i,
        (fderiv ℝ (fun y => fderiv ℝ (fun x => A x i j) y (b k)) z (b j) *
          J.value (i :: w) z +
         fderiv ℝ (fun y => A y i j) z (b k) * J.value (j :: i :: w) z)) ∧
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
        (∑ j, ∫ z in K, (∑ i, A z i j * J.value (k :: i :: w) z) *
          fderiv ℝ φ z (b j)) = -(∫ z in K, G z * φ z) := by
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
  have hf : MemLp (fun z => fderiv ℝ F z (b k)) 2 (volume.restrict K) := by
    exact memLp_localDirectionalIterate_on_compact b hK hW hKW hF [k]
  have he := (J.coefficient_derivative w hw hK hW hKW k A F hA
    (hF.of_le (by decide)) hPDE).2
  have he' : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (P j z + C j z) * fderiv ℝ φ z (b j)) =
        -(∫ z in K, fderiv ℝ F z (b k) * φ z) := by
    intro φ hφ hcφ hs
    have hh := he φ hφ hcφ hs
    have ha (j : ι) (z : E) : (∑ i,
        (fderiv ℝ (fun y => A y i j) z (b k) * J.value (i :: w) z +
          A z i j * J.value (k :: i :: w) z)) = P j z + C j z := by
      rw [Finset.sum_add_distrib]
      exact add_comm _ _
    simp_rw [ha] at hh
    exact hh
  obtain ⟨hg, heq⟩ := weak_divergence_remove_commutator b K P C dC
    (fun z => fderiv ℝ F z (b k)) hp (fun j => (hc j).1)
    (fun j => (hc j).2.1) hf (fun j => (hc j).2.2) he'
  exact ⟨_, hg, fun _ => rfl, heq⟩

end AlmostSchur
