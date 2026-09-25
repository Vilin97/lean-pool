/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Integrability

/-!
# Local Box

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- A compact subset of an open space-time carrier is contained in a compact
local box. -/
theorem caccioppoli_localBox_of_compact_subset
    {Ω : Set Vec3} {I : Set ℝ} {K : Set ParabolicPoint}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (hIord : I.OrdConnected)
    (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    ∃ Ω' J, localBox Ω I Ω' J ∧ K ⊆ spaceTimeSet Ω' J := by
  by_cases hKne : K.Nonempty
  · let Kx : Set Vec3 := Prod.fst '' K
    let Kt : Set ℝ := Prod.snd '' K
    have hKx : IsCompact Kx := hK.image continuous_fst_parabolicPoint
    have hKt : IsCompact Kt := hK.image continuous_snd_parabolicPoint
    have hKxsub : Kx ⊆ Ω := by
      rintro x ⟨z, hz, rfl⟩
      exact (hKsub hz).1
    have hKtsub : Kt ⊆ I := by
      rintro t ⟨z, hz, rfl⟩
      exact (hKsub hz).2
    obtain ⟨δE, hδE, hδEsub⟩ :=
      hKx.exists_cthickening_subset_open hΩ hKxsub
    obtain ⟨a, ha⟩ := hKt.exists_isLeast (hKne.image Prod.snd)
    obtain ⟨b, hb⟩ := hKt.exists_isGreatest (hKne.image Prod.snd)
    obtain ⟨la, ua, hau, hlua⟩ :=
      (mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds (hKtsub ha.1)))
    obtain ⟨lb, ub, hbu, hlub⟩ :=
      (mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds (hKtsub hb.1)))
    let l' : ℝ := (la + a) / 2
    let u' : ℝ := (b + ub) / 2
    have hll' : la < l' := by
      dsimp [l']
      linarith only [hau.1]
    have hla' : l' < a := by
      dsimp [l']
      linarith only [hau.1]
    have hbu' : b < u' := by
      dsimp [u']
      linarith only [hbu.2]
    have huub' : u' < ub := by
      dsimp [u']
      linarith only [hbu.2]
    have hlaI : l' ∈ I := hlua ⟨hll', hla'.trans hau.2⟩
    have hubI : u' ∈ I := hlub ⟨hbu.1.trans hbu', huub'⟩
    let Ω' : Set Vec3 := Metric.thickening (δE / 2) Kx
    let J : Set ℝ := Ioo l' u'
    have hΩ'open : IsOpen Ω' := Metric.isOpen_thickening
    have hΩ'compact : IsCompact (closure Ω') := by
      apply (hKx.cthickening).of_isClosed_subset isClosed_closure
      exact Metric.closure_thickening_subset_cthickening _ _
    have hΩ'sub : closure Ω' ⊆ Ω := by
      exact (Metric.closure_thickening_subset_cthickening _ _).trans
        ((Metric.cthickening_mono (by linarith only [hδE]) _).trans hδEsub)
    have hJord : J.OrdConnected := ordConnected_Ioo
    have hJcompact : IsCompact (closure J) := by
      have hab : l' < u' := lt_of_lt_of_le hla' (ha.2 hb.1) |>.trans hbu'
      rw [show closure J = Icc l' u' from closure_Ioo hab.ne]
      exact isCompact_Icc
    have hJsub : closure J ⊆ I := by
      have hab : l' < u' := lt_of_lt_of_le hla' (ha.2 hb.1) |>.trans hbu'
      rw [show closure J = Icc l' u' from closure_Ioo hab.ne]
      exact hIord.out hlaI hubI
    refine ⟨Ω', J, ⟨hΩ'open, hΩ'compact, hΩ'sub, hJord, hJcompact, hJsub⟩, ?_⟩
    rintro ⟨x, s⟩ hz
    refine ⟨Metric.self_subset_thickening (half_pos hδE) _ ⟨(x, s), hz, rfl⟩, ?_⟩
    exact ⟨hla'.trans_le (ha.2 ⟨(x, s), hz, rfl⟩),
      (hb.2 ⟨(x, s), hz, rfl⟩).trans_lt hbu'⟩
  · refine ⟨∅, ∅, ?_, ?_⟩
    · exact ⟨isOpen_empty, by simp, by simp, ordConnected_empty, by simp, by simp⟩
    · have hKeq : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
      rw [hKeq]
      exact empty_subset _

end CKN
