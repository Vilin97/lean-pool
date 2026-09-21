/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamSection9
import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.LpInfiniteDimensional
import LeanPool.DavisKahan.ForTauCeti.Order.DiscreteEnumeration

/-! # Beam Eigenvalue Sequence -/

open TauCeti.DavisKahan.Angle


/-!
# The free beam's eigenvalues are an unbounded increasing sequence

`BeamSection9` exhibits *one* spectral point of `beamOperator` above `500`.  Davis--Kahan 1970
Section 9 prints an increasing *sequence* `α₃ < α₄ < …`.  The single missing input was that the
ambient space is infinite-dimensional; with it the compact variational resolvent does the rest.

The chain is:

* `TauCeti.not_finiteDimensional_lpTwo_unitIocMeasure` (ForTauCeti) makes `BeamL2`
  infinite-dimensional — the indicators of the disjoint intervals `(1/(n+2), 1/(n+1)]` are an
  infinite orthogonal family;
* `TauCeti.exists_hasEigenvalue_norm_lt` (ForTauCeti) then forces the compact self-adjoint
  injective resolvent to have eigenvalues of arbitrarily small modulus: finitely many
  eigenvalues of modulus `≥ c` would make the span of the eigenspaces finite-dimensional,
  hence closed, hence everything;
* `beamResolvent_eigenvalue_classify` turns each such resolvent eigenvalue `μ = (1+β⁴)⁻¹`
  into the operator eigenvalue `β⁴`, which is *large* exactly because `μ` is *small*.

## What is and is not proved

Proved: the real spectrum of `beamOperator` is unbounded above; there are infinitely many
spectral points above `500`; the set `beamEigenvalues` of positive *eigenvalues* is both
unbounded above and finite below every bound; and — the printed statement — that set *is* a
strictly increasing sequence: `beamEigenvalues` is order-isomorphic to `ℕ`, and the
enumeration `f : ℕ → ℝ` is strictly monotone with `Set.range f = beamEigenvalues`, every term
above `500` and in `TauCeti.LinearPMap.realSpectrum beamOperator`.  Nothing is omitted from the list and nothing
outside `beamEigenvalues` is in it.

The order bookkeeping is `TauCeti.exists_strictMono_range_eq_of_unbounded_of_finite_inter_Iic`
(ForTauCeti), which is general: unbounded above plus finite below every bound is exactly
"order-isomorphic to `ℕ`" for a subset of any linear order.

Also proved, and this closes the last gap the previous pass recorded: the free beam has *no*
continuous or residual real spectrum.  `exists_eigenvector_of_mem_realSpectrum_beamOperator`
(BeamSpectrum) produces an eigenvector for every real spectral point, so
`TauCeti.LinearPMap.realSpectrum beamOperator = insert 0 beamEigenvalues` exactly, and local finiteness holds for
the whole real spectrum and not only for the point spectrum.

## Main results

* `TauCeti.…FreeBeam.Model.not_finiteDimensional_beamL2`: the ambient space is
  infinite-dimensional.
* `TauCeti.…FreeBeam.Model.exists_lt_five_hundred_lt_mem_realSpectrum_beamOperator`: a
  spectral point above any prescribed bound.
* `TauCeti.…FreeBeam.Model.exists_strictMono_mem_realSpectrum_beamOperator`: the increasing
  sequence.
* `TauCeti.…FreeBeam.Model.finite_beamEigenvalues_inter_Iic`: the eigenvalues are discrete.
* `TauCeti.…FreeBeam.Model.exists_strictMono_range_eq_beamEigenvalues`: the increasing
  sequence *enumerates* the eigenvalues.
* `TauCeti.…FreeBeam.Model.realSpectrum_beamOperator_eq_insert_zero`: the real spectrum is
  exactly `{0}` together with those eigenvalues.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model

noncomputable section

/-! ## The ambient space is infinite-dimensional -/

/-- **`BeamL2` is infinite-dimensional.**  This is the one input Section 9's eigenvalue
*sequence* needed and the repository did not have: `realSpectrum_beamOperator_subset_gap` is
an upper-bound-free containment, and even with a nonempty positive spectrum nothing forced a
second eigenvalue until the ambient space was known to be infinite-dimensional. -/
theorem not_finiteDimensional_beamL2 : ¬ FiniteDimensional ℂ BeamL2 :=
  TauCeti.not_finiteDimensional_lpTwo_unitIocMeasure

/-- The variational resolvent has no kernel, so `0` is not one of its eigenvalues. -/
theorem eigenspace_beamResolvent_zero_eq_bot :
    Module.End.eigenspace beamCoerciveFormData.resolvent.toLinearMap 0 = ⊥ := by
  rw [Module.End.eigenspace_zero]
  exact LinearMap.ker_eq_bot.mpr beamCoerciveFormData.resolvent_injective

/-! ## Eigenvalues above every bound -/

/-- **The free beam has a positive eigenvalue above any prescribed bound.**  The resolvent is
compact, self-adjoint and injective on an infinite-dimensional space, so it has eigenvalues of
arbitrarily small modulus; the classification of its nonzero eigenvalues inverts each one into
an eigenvalue `β⁴` of `beamOperator`, and a small resolvent eigenvalue is a large `β⁴`. -/
theorem exists_pos_eigenpair_beamOperator_gt (M : ℝ) :
    ∃ (lam : ℝ) (x : beamOperator.domain), M < lam ∧ 0 < lam ∧ (x : BeamL2) ≠ 0 ∧
      beamOperator x = (lam : ℂ) • (x : BeamL2) := by
  set N : ℝ := max M 0 with hNdef
  have hMN : M ≤ N := le_max_left _ _
  have hN0 : (0 : ℝ) ≤ N := le_max_right _ _
  have hNpos : (0 : ℝ) < 1 + N := by linarith
  have hc : (0 : ℝ) < (1 + N)⁻¹ := inv_pos.mpr hNpos
  have hNinv : (1 + N)⁻¹ * (1 + N) = 1 := inv_mul_cancel₀ (ne_of_gt hNpos)
  obtain ⟨mu, hev, hmu0, hmunorm⟩ :=
    TauCeti.exists_hasEigenvalue_norm_lt isCompactOperator_beamResolvent
      beamCoerciveFormData.resolvent_isSelfAdjoint eigenspace_beamResolvent_zero_eq_bot
      not_finiteDimensional_beamL2 hc
  obtain ⟨u, hu, hu0⟩ := hev.exists_hasEigenvector
  have hRu : beamCoerciveFormData.resolvent u = mu • u := Module.End.mem_eigenspace_iff.mp hu
  rcases beamResolvent_eigenvalue_classify hmu0 hu0 hRu with h1 | ⟨beta, hbeta, hchar, hmueq⟩
  · -- the resolvent eigenvalue `1` has modulus `1`, too big to be below `(1+N)⁻¹ ≤ 1`
    exfalso
    rw [h1, norm_one] at hmunorm
    have hstep : 1 * (1 + N) < (1 + N)⁻¹ * (1 + N) :=
      mul_lt_mul_of_pos_right hmunorm hNpos
    rw [hNinv, one_mul] at hstep
    linarith
  · have hb4 : (0 : ℝ) < 1 + beta ^ 4 := by positivity
    have hbinv : (1 + beta ^ 4)⁻¹ * (1 + beta ^ 4) = 1 := inv_mul_cancel₀ (ne_of_gt hb4)
    have hbpos : (0 : ℝ) < (1 + beta ^ 4)⁻¹ := inv_pos.mpr hb4
    -- the modulus of the resolvent eigenvalue is `(1+β⁴)⁻¹`
    have hnorm : ‖mu‖ = (1 + beta ^ 4)⁻¹ := by
      rw [hmueq, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hbpos)]
    rw [hnorm] at hmunorm
    have hxB : (1 + beta ^ 4)⁻¹ * (1 + N) < 1 := by
      have hstep := mul_lt_mul_of_pos_right hmunorm hNpos
      rwa [hNinv] at hstep
    have hAB : (1 + N) < 1 + beta ^ 4 :=
      lt_of_mul_lt_mul_left (by rw [hbinv]; exact hxB) (le_of_lt hbpos)
    have hkey : M < beta ^ 4 := by linarith
    have hb4pos : (0 : ℝ) < beta ^ 4 := by positivity
    obtain ⟨humem, hbeam⟩ := exists_beamOperator_apply_of_beamResolvent_smul hmu0 hRu
    have hinv : mu⁻¹ - 1 = ((beta ^ 4 : ℝ) : ℂ) := by
      have hposc : ((1 + beta ^ 4 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb4.ne'
      rw [hmueq, show ((((1 + beta ^ 4)⁻¹ : ℝ)) : ℂ) = (((1 + beta ^ 4 : ℝ) : ℂ))⁻¹ from by
        push_cast; ring, inv_inv]
      push_cast
      ring
    refine ⟨beta ^ 4, ⟨u, humem⟩, hkey, hb4pos, hu0, ?_⟩
    rw [hbeam, hinv]

/-- **A real spectral point of the free beam above any prescribed bound**, still above the
paper's `500`.  This is the unbounded half of Section 9's printed sequence
`α₃ < α₄ < …`. -/
theorem exists_lt_five_hundred_lt_mem_realSpectrum_beamOperator (M : ℝ) :
    ∃ alpha : ℝ, M < alpha ∧ 500 < alpha ∧ alpha ∈ TauCeti.LinearPMap.realSpectrum beamOperator := by
  obtain ⟨lam, x, hM, hlam, hx0, heig⟩ := exists_pos_eigenpair_beamOperator_gt M
  exact ⟨lam, hM, eigenvalue_gt_five_hundred hlam hx0 heig,
    TauCeti.LinearPMap.mem_realSpectrum_of_eigenvector (A := beamOperator)
      (x := x) hx0 heig⟩

/-- **The real spectrum of the free beam is unbounded above.** -/
theorem not_bddAbove_realSpectrum_beamOperator :
    ¬ BddAbove (TauCeti.LinearPMap.realSpectrum beamOperator) := by
  rintro ⟨b, hb⟩
  obtain ⟨alpha, hM, -, hmem⟩ := exists_lt_five_hundred_lt_mem_realSpectrum_beamOperator b
  exact absurd (hb hmem) (not_le.mpr hM)

/-! ## The eigenvalues are discrete -/

/-- The set of positive eigenvalues of the free-beam operator.  Every element exceeds `500`
(`eigenvalue_gt_five_hundred`) and lies in `TauCeti.LinearPMap.realSpectrum beamOperator`. -/
def beamEigenvalues : Set ℝ :=
  {lam : ℝ | 0 < lam ∧ ∃ x : beamOperator.domain, (x : BeamL2) ≠ 0 ∧
    beamOperator x = (lam : ℂ) • (x : BeamL2)}

/-- Every positive eigenvalue of the free beam exceeds the paper's `500`. -/
theorem five_hundred_lt_of_mem_beamEigenvalues {lam : ℝ} (hlam : lam ∈ beamEigenvalues) :
    500 < lam := by
  obtain ⟨hpos, x, hx0, heig⟩ := hlam
  exact eigenvalue_gt_five_hundred hpos hx0 heig

/-- Every positive eigenvalue of the free beam is a point of its real spectrum. -/
theorem mem_realSpectrum_of_mem_beamEigenvalues {lam : ℝ} (hlam : lam ∈ beamEigenvalues) :
    lam ∈ TauCeti.LinearPMap.realSpectrum beamOperator := by
  obtain ⟨-, x, hx0, heig⟩ := hlam
  exact TauCeti.LinearPMap.mem_realSpectrum_of_eigenvector (A := beamOperator)
    (x := x) hx0 heig

/-- **The eigenvalue relation inverts.**  An eigenvector of `beamOperator` for `lam` is an
eigenvector of the variational resolvent for `(1 + lam)⁻¹`; this is the converse of
`exists_beamOperator_apply_of_beamResolvent_smul` and is what transfers the discreteness of
the resolvent's spectrum back to the operator. -/
theorem beamResolvent_apply_of_beamOperator_eigen {lam : ℝ} (hlam : 0 < lam)
    {x : beamOperator.domain}
    (heig : beamOperator x = (lam : ℂ) • (x : BeamL2)) :
    beamCoerciveFormData.resolvent (x : BeamL2)
      = (((1 + lam : ℝ) : ℂ))⁻¹ • (x : BeamL2) := by
  have hne : ((1 + lam : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 1 + lam := by linarith
    exact_mod_cast this.ne'
  have hz := Abstract.R_inversePartialMap_apply beamCoerciveFormData.resolvent
    beamCoerciveFormData.resolvent_isSelfAdjoint beamCoerciveFormData.resolvent_injective x
  have hsplit : beamShiftedFormData.shiftedOperator x
      = beamOperator x + (x : BeamL2) := by
    have h : beamOperator x
        = beamShiftedFormData.shiftedOperator x - (x : BeamL2) :=
      beamShiftedFormData.beamOperator_apply _
    rw [h]
    abel
  have hshift : beamShiftedFormData.shiftedOperator x
      = ((1 + lam : ℝ) : ℂ) • (x : BeamL2) := by
    rw [hsplit, heig]
    push_cast
    rw [add_smul, one_smul]
    abel
  have hRx : ((1 + lam : ℝ) : ℂ) • beamCoerciveFormData.resolvent (x : BeamL2)
      = (x : BeamL2) := by
    rw [← map_smul, ← hshift]
    exact hz
  have hcancel := congrArg (fun v : BeamL2 => (((1 + lam : ℝ) : ℂ))⁻¹ • v) hRx
  simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at hcancel
  exact hcancel

/-- **The free beam has only finitely many eigenvalues below any bound.**  Together with
`exists_pos_eigenpair_beamOperator_gt` this says the positive eigenvalues form a discrete
unbounded subset of `(500, ∞)` — the content of Davis--Kahan Section 9's printed
`α₃ < α₄ < …`.

The bridge is that `lam ↦ (1 + lam)⁻¹` carries eigenvalues of `beamOperator` injectively into
eigenvalues of the compact resolvent, and `lam ≤ M` becomes `(1 + M)⁻¹ ≤ ‖(1 + lam)⁻¹‖`, a
region where a compact self-adjoint operator has only finitely many eigenvalues. -/
theorem finite_beamEigenvalues_inter_Iic (M : ℝ) :
    (beamEigenvalues ∩ Set.Iic M).Finite := by
  rcases le_or_gt M 0 with hM | hM
  · refine Set.Finite.subset (Set.finite_empty) ?_
    rintro lam ⟨⟨hpos, -⟩, hle⟩
    exact absurd (lt_of_lt_of_le hpos hle) (not_lt.mpr hM)
  · have hMpos : (0 : ℝ) < 1 + M := by linarith
    have hc : (0 : ℝ) < (1 + M)⁻¹ := inv_pos.mpr hMpos
    set F : ℝ → ℂ := fun lam => (((1 + lam : ℝ) : ℂ))⁻¹ with hFdef
    have hfinS := TauCeti.finite_setOf_hasEigenvalue_le_norm isCompactOperator_beamResolvent
      beamCoerciveFormData.resolvent_isSelfAdjoint hc
    -- the image lands inside the finite set of large resolvent eigenvalues
    have himg : F '' (beamEigenvalues ∩ Set.Iic M) ⊆
        {mu : ℂ | Module.End.HasEigenvalue beamCoerciveFormData.resolvent.toLinearMap mu ∧
          (1 + M)⁻¹ ≤ ‖mu‖} := by
      rintro _ ⟨lam, ⟨⟨hpos, x, hx0, heig⟩, hle⟩, rfl⟩
      have hleM : lam ≤ M := hle
      have hlpos : (0 : ℝ) < 1 + lam := by linarith
      have hres := beamResolvent_apply_of_beamOperator_eigen hpos heig
      have hmem : (x : BeamL2) ∈
          Module.End.eigenspace beamCoerciveFormData.resolvent.toLinearMap (F lam) :=
        Module.End.mem_eigenspace_iff.mpr hres
      refine ⟨?_, ?_⟩
      · rw [Module.End.hasEigenvalue_iff]
        intro hbot
        exact hx0 (Submodule.mem_bot ℂ |>.mp (hbot ▸ hmem))
      · have hFnorm : ‖F lam‖ = (1 + lam)⁻¹ := by
          rw [hFdef]
          simp only [← Complex.ofReal_inv, Complex.norm_real]
          exact Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hlpos))
        rw [hFnorm]
        have hstep : (1 + lam)⁻¹ * ((1 + lam) * (1 + M))
            ≥ (1 + M)⁻¹ * ((1 + lam) * (1 + M)) := by
          rw [show (1 + lam)⁻¹ * ((1 + lam) * (1 + M)) = ((1 + lam)⁻¹ * (1 + lam)) * (1 + M) from
            by ring, inv_mul_cancel₀ hlpos.ne', one_mul,
            show (1 + M)⁻¹ * ((1 + lam) * (1 + M)) = ((1 + M)⁻¹ * (1 + M)) * (1 + lam) from
            by ring, inv_mul_cancel₀ hMpos.ne', one_mul]
          linarith
        have hprodpos : (0 : ℝ) < (1 + lam) * (1 + M) := mul_pos hlpos hMpos
        exact le_of_mul_le_mul_right (by linarith) hprodpos
    have hinj : Set.InjOn F (beamEigenvalues ∩ Set.Iic M) := by
      rintro a ⟨⟨ha, -⟩, -⟩ b ⟨⟨hb, -⟩, -⟩ hab
      have hapos : (0 : ℝ) < 1 + a := by linarith
      have hbpos : (0 : ℝ) < 1 + b := by linarith
      rw [hFdef] at hab
      simp only [← Complex.ofReal_inv, Complex.ofReal_inj] at hab
      have : (1 : ℝ) + a = 1 + b := by
        have := congrArg (fun t : ℝ => t⁻¹) hab
        simpa [inv_inv] using this
      linarith
    exact Set.Finite.of_finite_image (hfinS.subset himg) hinj

/-- **The positive eigenvalues of the free beam are unbounded above.** -/
theorem exists_lt_mem_beamEigenvalues (M : ℝ) : ∃ lam ∈ beamEigenvalues, M < lam := by
  obtain ⟨lam, x, hM, hpos, hx0, heig⟩ := exists_pos_eigenpair_beamOperator_gt M
  exact ⟨lam, ⟨hpos, x, hx0, heig⟩, hM⟩

/-! ## The increasing sequence -/

/-- **Davis--Kahan Section 9's increasing sequence of eigenvalues.**  A strictly increasing
sequence of real spectral points of the free-beam operator, every term above the paper's
`500`.  Each term is produced from the previous one by the unbounded-spectrum theorem, so the
sequence is increasing by construction; it is not claimed to enumerate the positive spectrum
in order. -/
theorem exists_strictMono_mem_realSpectrum_beamOperator :
    ∃ f : ℕ → ℝ, StrictMono f ∧ ∀ n, 500 < f n ∧ f n ∈ TauCeti.LinearPMap.realSpectrum beamOperator := by
  classical
  set g : ℝ → ℝ :=
    fun M => (exists_lt_five_hundred_lt_mem_realSpectrum_beamOperator M).choose with hgdef
  have hg1 : ∀ M : ℝ, M < g M := fun M =>
    (exists_lt_five_hundred_lt_mem_realSpectrum_beamOperator M).choose_spec.1
  have hg2 : ∀ M : ℝ, 500 < g M := fun M =>
    (exists_lt_five_hundred_lt_mem_realSpectrum_beamOperator M).choose_spec.2.1
  have hg3 : ∀ M : ℝ, g M ∈ TauCeti.LinearPMap.realSpectrum beamOperator := fun M =>
    (exists_lt_five_hundred_lt_mem_realSpectrum_beamOperator M).choose_spec.2.2
  refine ⟨fun n => Nat.rec (motive := fun _ => ℝ) (g 500) (fun _ prev => g prev) n, ?_, ?_⟩
  · exact strictMono_nat_of_lt_succ fun n => hg1 _
  · intro n
    cases n with
    | zero => exact ⟨hg2 500, hg3 500⟩
    | succ k => exact ⟨hg2 _, hg3 _⟩

/-! ## The full real spectrum -/

/-- **`0` is in the real spectrum of the free beam.**  The constant function is a nonzero
element of the affine kernel — `norm_affineLp_sq` makes `‖affineLp 1 0‖ ^ 2 = 1`. -/
theorem zero_mem_realSpectrum_beamOperator : (0 : ℝ) ∈ TauCeti.LinearPMap.realSpectrum beamOperator := by
  obtain ⟨hmem, hzero⟩ := beamOperator_affine_mem_and_zero 1 0
  set x : beamOperator.domain := ⟨affineLp 1 0, hmem⟩ with hxdef
  have hne : (x : BeamL2) ≠ 0 := by
    rw [hxdef]
    intro h0
    have hnorm := norm_affineLp_sq 1 0
    rw [show affineLp 1 0 = 0 from h0, norm_zero] at hnorm
    norm_num at hnorm
  have heig : beamOperator x = ((0 : ℝ) : ℂ) • (x : BeamL2) := by
    rw [hzero, Complex.ofReal_zero, zero_smul]
  exact TauCeti.LinearPMap.mem_realSpectrum_of_eigenvector (A := beamOperator)
    (x := x) hne heig

/-- **The real spectrum of the free beam is exactly `{0}` together with the positive
eigenvalues.**  `exists_eigenvector_of_mem_realSpectrum_beamOperator` says every spectral point
is an eigenvalue and `nonneg_of_beamOperator_eigen` says every eigenvalue is nonnegative, so
there is no continuous or residual spectrum to account for. -/
theorem realSpectrum_beamOperator_eq_insert_zero :
    TauCeti.LinearPMap.realSpectrum beamOperator = insert 0 beamEigenvalues := by
  apply Set.Subset.antisymm
  · intro lam hlam
    obtain ⟨x, hx0, heig⟩ := exists_eigenvector_of_mem_realSpectrum_beamOperator hlam
    rcases eq_or_lt_of_le (nonneg_of_beamOperator_eigen hx0 heig) with h0 | hpos
    · exact Set.mem_insert_iff.mpr (Or.inl h0.symm)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨hpos, x, hx0, heig⟩)
  · intro lam hlam
    rcases Set.mem_insert_iff.mp hlam with rfl | hlam'
    · exact zero_mem_realSpectrum_beamOperator
    · exact mem_realSpectrum_of_mem_beamEigenvalues hlam'

/-- **The free beam has only finitely many spectral points below any bound.**  This is
`finite_beamEigenvalues_inter_Iic` upgraded from the point spectrum to the whole real
spectrum, which the previous statement could not reach. -/
theorem finite_realSpectrum_beamOperator_inter_Iic (M : ℝ) :
    (TauCeti.LinearPMap.realSpectrum beamOperator ∩ Set.Iic M).Finite := by
  refine Set.Finite.subset (Set.Finite.insert 0 (finite_beamEigenvalues_inter_Iic M)) ?_
  rw [realSpectrum_beamOperator_eq_insert_zero]
  rintro lam ⟨hlam, hle⟩
  rcases Set.mem_insert_iff.mp hlam with rfl | hlam'
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_iff.mpr (Or.inr ⟨hlam', hle⟩)

/-! ## The printed enumeration -/

/-- **The eigenvalues of the free beam are order-isomorphic to `ℕ`.**  The two facts proved
above — unbounded above (`exists_lt_mem_beamEigenvalues`) and finite below every bound
(`finite_beamEigenvalues_inter_Iic`) — are exactly the hypotheses under which a subset of a
linear order is a strictly increasing sequence. -/
theorem nonempty_orderIso_nat_beamEigenvalues : Nonempty (↥beamEigenvalues ≃o ℕ) :=
  TauCeti.nonempty_orderIso_nat_of_unbounded_of_finite_inter_Iic
    exists_lt_mem_beamEigenvalues finite_beamEigenvalues_inter_Iic

/-- **Davis--Kahan Section 9's printed sequence `α₃ < α₄ < …`, as an enumeration.**  There is a
strictly increasing `f : ℕ → ℝ` whose range is *exactly* the set of positive eigenvalues of the
free-beam operator, with every term above the paper's `500` and in the real spectrum.  Unlike
`exists_strictMono_mem_realSpectrum_beamOperator`, which merely picks an increasing subsequence
of spectral points, this omits no eigenvalue and lists nothing else. -/
theorem exists_strictMono_range_eq_beamEigenvalues :
    ∃ f : ℕ → ℝ, StrictMono f ∧ Set.range f = beamEigenvalues ∧
      ∀ n, 500 < f n ∧ f n ∈ TauCeti.LinearPMap.realSpectrum beamOperator := by
  obtain ⟨f, hmono, hrange⟩ :=
    TauCeti.exists_strictMono_range_eq_of_unbounded_of_finite_inter_Iic
      exists_lt_mem_beamEigenvalues finite_beamEigenvalues_inter_Iic
  refine ⟨f, hmono, hrange, fun n => ?_⟩
  have hmem : f n ∈ beamEigenvalues := by
    rw [← hrange]
    exact Set.mem_range_self n
  exact ⟨five_hundred_lt_of_mem_beamEigenvalues hmem,
    mem_realSpectrum_of_mem_beamEigenvalues hmem⟩

/-- **The free beam has infinitely many spectral points above `500`.** -/
theorem infinite_five_hundred_lt_mem_realSpectrum_beamOperator :
    {alpha : ℝ | 500 < alpha ∧ alpha ∈ TauCeti.LinearPMap.realSpectrum beamOperator}.Infinite := by
  obtain ⟨f, hf, hmem⟩ := exists_strictMono_mem_realSpectrum_beamOperator
  exact Set.infinite_of_injective_forall_mem hf.injective hmem

end

end Model
end FreeBeam
end DavisKahan
end TauCeti
