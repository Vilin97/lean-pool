/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondOperator
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Normed.Operator.Mul
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ExtensionNormTransport

/-!
# Lp Extension

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/- The dense domain consists of `L^p` classes which also have an `L²`
   representative. -/
def lpInterL2Submodule (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Submodule ℝ (Lp ℝ p (volume : Measure Vec3)) where
  carrier := {u | MemLp (u : Vec3 → ℝ) (2 : ℝ≥0∞) volume}
  zero_mem' := by
    show MemLp ((0 : Lp ℝ p volume) : Vec3 → ℝ) (2 : ℝ≥0∞) volume
    exact memLp_congr_ae (Lp.coeFn_zero ℝ p volume :
      ((0 : Lp ℝ p volume) : Vec3 → ℝ) =ᵐ[volume] 0) |>.2 MemLp.zero
  add_mem' := by
    intro u v hu hv
    exact memLp_congr_ae (Lp.coeFn_add (u : Lp ℝ p volume) (v : Lp ℝ p volume)) |>.2
      (hu.add hv)
  smul_mem' := by
    intro c u hu
    exact memLp_congr_ae (Lp.coeFn_smul c (u : Lp ℝ p volume)) |>.2 (hu.const_smul c)

private lemma lpInterL2_dense {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {u : Lp ℝ p (volume : Measure Vec3) |
      u ∈ lpInterL2Submodule p} := by
  intro u
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 ?_
  intro ε hε
  have hεE : ENNReal.ofReal ε ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hε
  obtain ⟨g, hgSupp, hgSub, hgCont, hgMem⟩ :=
    (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le hp hεE
  have hg₂ : MemLp g (2 : ℝ≥0∞) volume :=
    hgCont.memLp_of_hasCompactSupport hgSupp
  let v : Lp ℝ p (volume : Measure Vec3) := hgMem.toLp g
  have hv₂ : MemLp (v : Vec3 → ℝ) (2 : ℝ≥0∞) volume := by
    exact memLp_congr_ae hgMem.coeFn_toLp |>.2 hg₂
  have hv_mem : v ∈ lpInterL2Submodule p := hv₂
  refine ⟨v, hv_mem, ?_⟩
  rw [Metric.mem_closedBall, dist_comm, Lp.dist_def]
  have hsub : eLpNorm ((u : Vec3 → ℝ) - (v : Vec3 → ℝ)) p volume ≤
      ENNReal.ofReal ε := by
    change eLpNorm ((u : Vec3 → ℝ) -
      ((hgMem.toLp g : Lp ℝ p volume) : Vec3 → ℝ)) p volume ≤ ENNReal.ofReal ε
    calc
      eLpNorm ((u : Vec3 → ℝ) -
          ((hgMem.toLp g : Lp ℝ p volume) : Vec3 → ℝ)) p volume =
          eLpNorm ((u : Vec3 → ℝ) - g) p volume :=
        eLpNorm_congr_ae (EventuallyEq.sub EventuallyEq.rfl hgMem.coeFn_toLp)
      _ ≤ ENNReal.ofReal ε := hgSub
  have hfinite : eLpNorm ((u : Vec3 → ℝ) - (v : Vec3 → ℝ)) p volume ≠ ∞ :=
    (Lp.memLp u).sub (Lp.memLp v) |>.eLpNorm_ne_top
  exact (ENNReal.le_ofReal_iff_toReal_le hfinite hε.le).1 hsub

structure LpExtensionInput (p : ℝ≥0∞) (C : ℝ) where
  T : (Vec3 → ℝ) → Vec3 → ℝ
  measurable : ∀ {f : Vec3 → ℝ}, MemLp f (2 : ℝ≥0∞) volume → Measurable (T f)
  output_mem : ∀ {f : Vec3 → ℝ}, MemLp f p volume →
    MemLp f (2 : ℝ≥0∞) volume →
    MemLp (T f) p volume
  congr_ae : ∀ {f g : Vec3 → ℝ}, MemLp f (2 : ℝ≥0∞) volume →
    MemLp g (2 : ℝ≥0∞) volume → f =ᵐ[volume] g → T f =ᵐ[volume] T g
  add_ae : ∀ {f g : Vec3 → ℝ}, MemLp f (2 : ℝ≥0∞) volume →
    MemLp g (2 : ℝ≥0∞) volume → T (f + g) =ᵐ[volume] T f + T g
  smul_ae : ∀ (c : ℝ) {f : Vec3 → ℝ}, MemLp f (2 : ℝ≥0∞) volume →
    T (c • f) =ᵐ[volume] c • T f
  bound : ∀ {f : Vec3 → ℝ} (hf : MemLp f p volume)
    (hf₂ : MemLp f (2 : ℝ≥0∞) volume),
    ‖(output_mem hf hf₂).toLp (T f)‖ ≤
      C * ‖hf.toLp f‖

def lpInterL2Map {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (h : LpExtensionInput p C) :
    lpInterL2Submodule p →ₗ[ℝ] Lp ℝ p (volume : Measure Vec3) where
  toFun u :=
    (h.output_mem (Lp.memLp (u : Lp ℝ p volume))
      (show MemLp (u : Vec3 → ℝ) (2 : ℝ≥0∞) volume from u.property)).toLp
      (h.T (u : Vec3 → ℝ))
  map_add' := by
    intro u v
    let uL : Lp ℝ p volume := u.1
    let vL : Lp ℝ p volume := v.1
    let hu : MemLp (uL : Vec3 → ℝ) (2 : ℝ≥0∞) volume := u.property
    let hv : MemLp (vL : Vec3 → ℝ) (2 : ℝ≥0∞) volume := v.property
    have hu0 : MemLp (u : Vec3 → ℝ) (2 : ℝ≥0∞) volume := by
      simpa only [uL] using hu
    have hv0 : MemLp (v : Vec3 → ℝ) (2 : ℝ≥0∞) volume := by
      simpa only [vL] using hv
    have hu_p : MemLp (uL : Vec3 → ℝ) p volume := Lp.memLp uL
    have hv_p : MemLp (vL : Vec3 → ℝ) p volume := Lp.memLp vL
    have huv : MemLp ((uL : Vec3 → ℝ) + (vL : Vec3 → ℝ))
        (2 : ℝ≥0∞) volume := hu.add hv
    have hcoe : (((u + v : lpInterL2Submodule p) : Vec3 → ℝ)) =ᵐ[volume]
        (uL : Vec3 → ℝ) + (vL : Vec3 → ℝ) := Lp.coeFn_add uL vL
    have huv0 : MemLp ((u + v : lpInterL2Submodule p) : Vec3 → ℝ)
        (2 : ℝ≥0∞) volume := memLp_congr_ae hcoe |>.2 huv
    have huv_p : MemLp ((u + v : lpInterL2Submodule p) : Vec3 → ℝ) p volume :=
      memLp_congr_ae hcoe |>.2 ((Lp.memLp uL).add (Lp.memLp vL))
    have hTcoe := h.congr_ae huv0 huv hcoe
    have hTadd := h.add_ae hu hv
    apply Lp.ext
    calc
      ((h.output_mem huv_p huv0).toLp
          (h.T ((u + v : lpInterL2Submodule p) : Vec3 → ℝ)) :
          Vec3 → ℝ) =ᵐ[volume] h.T ((u + v : lpInterL2Submodule p) : Vec3 → ℝ) :=
        (h.output_mem huv_p huv0).coeFn_toLp
      _ =ᵐ[volume] h.T ((uL : Vec3 → ℝ) + (vL : Vec3 → ℝ)) := hTcoe
      _ =ᵐ[volume] h.T (uL : Vec3 → ℝ) + h.T (vL : Vec3 → ℝ) := hTadd
      _ =ᵐ[volume]
          ((h.output_mem hu_p hu0).toLp (h.T (u : Vec3 → ℝ)) : Vec3 → ℝ) +
            ((h.output_mem hv_p hv0).toLp (h.T (v : Vec3 → ℝ)) : Vec3 → ℝ) :=
        ((h.output_mem hu_p hu0).coeFn_toLp.add (h.output_mem hv_p hv0).coeFn_toLp).symm
      _ =ᵐ[volume] _ := by
        exact (Lp.coeFn_add
          ((h.output_mem hu_p hu0).toLp (h.T (u : Vec3 → ℝ)))
          ((h.output_mem hv_p hv0).toLp (h.T (v : Vec3 → ℝ)))).symm
  map_smul' := by
    intro c u
    let uL : Lp ℝ p volume := u.1
    let hu : MemLp (uL : Vec3 → ℝ) (2 : ℝ≥0∞) volume := u.property
    have hu0 : MemLp (u : Vec3 → ℝ) (2 : ℝ≥0∞) volume := by
      simpa only [uL] using hu
    have hu_p : MemLp (uL : Vec3 → ℝ) p volume := Lp.memLp uL
    have hcoe : (((c • u : lpInterL2Submodule p) : Vec3 → ℝ)) =ᵐ[volume]
        c • (uL : Vec3 → ℝ) := Lp.coeFn_smul c uL
    have hcu0 : MemLp ((c • u : lpInterL2Submodule p) : Vec3 → ℝ)
        (2 : ℝ≥0∞) volume := memLp_congr_ae hcoe |>.2 (hu.const_smul c)
    have hcu_p : MemLp ((c • u : lpInterL2Submodule p) : Vec3 → ℝ) p volume :=
      memLp_congr_ae hcoe |>.2 ((Lp.memLp uL).const_smul c)
    have hTcoe := h.congr_ae hcu0 (hu.const_smul c) hcoe
    have hTsmul := h.smul_ae c hu
    apply Lp.ext
    calc
      ((h.output_mem hcu_p hcu0).toLp
          (h.T ((c • u : lpInterL2Submodule p) : Vec3 → ℝ)) : Vec3 → ℝ) =ᵐ[volume]
          h.T ((c • u : lpInterL2Submodule p) : Vec3 → ℝ) :=
        (h.output_mem hcu_p hcu0).coeFn_toLp
      _ =ᵐ[volume] h.T (c • (uL : Vec3 → ℝ)) := hTcoe
      _ =ᵐ[volume] c • h.T (uL : Vec3 → ℝ) := hTsmul
      _ =ᵐ[volume] c • ((h.output_mem hu_p hu0).toLp
          (h.T (u : Vec3 → ℝ)) : Vec3 → ℝ) :=
        ((h.output_mem hu_p hu0).coeFn_toLp.const_smul c).symm
      _ =ᵐ[volume] _ := by
        simpa only [RingHom.id_apply] using
          (Lp.coeFn_smul c ((h.output_mem hu_p hu0).toLp (h.T (u : Vec3 → ℝ)))).symm

private lemma lpInterL2Map_bound {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (h : LpExtensionInput p C) (u : lpInterL2Submodule p) :
    ‖lpInterL2Map h u‖ ≤ C * ‖u‖ := by
  let uL : Lp ℝ p volume := u.1
  let hf : MemLp (uL : Vec3 → ℝ) p volume := Lp.memLp uL
  have hbound := h.bound hf u.property
  have hto : hf.toLp (uL : Vec3 → ℝ) = uL := Lp.ext hf.coeFn_toLp
  rw [hto] at hbound
  change ‖(h.output_mem hf
      (show MemLp (u : Vec3 → ℝ) (2 : ℝ≥0∞) volume from u.property)).toLp
      (h.T (u : Vec3 → ℝ))‖ ≤ C * ‖u‖
  simpa only [uL, Submodule.norm_coe] using hbound

private lemma lpInterL2Map_bound_subtype {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (h : LpExtensionInput p C) :
    ∀ v : lpInterL2Submodule p,
      ‖lpInterL2Map h v‖ ≤ C * ‖(lpInterL2Submodule p).subtype v‖ := by
  intro v
  simpa only [Submodule.subtype_apply, Submodule.norm_coe] using
    lpInterL2Map_bound h v

def lpExtensionCore {p : ℝ≥0∞} [Fact (1 ≤ p)] {C : ℝ} (hp : p ≠ ∞)
    (h : LpExtensionInput p C) :
    Lp ℝ p (volume : Measure Vec3) →L[ℝ] Lp ℝ p (volume : Measure Vec3) :=
  LinearMap.mkContinuous
    ((lpInterL2Map h).extendOfNorm (lpInterL2Submodule p).subtype)
    C (by
      intro u
      exact LinearMap.norm_extendOfNorm_apply_le
        (denseRange_subtype_val.mpr (lpInterL2_dense (p := p) hp))
        C (lpInterL2Map_bound_subtype h) u)

theorem lpExtensionCore_agrees {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C)
    (u : lpInterL2Submodule p) :
    lpExtensionCore hp h u = lpInterL2Map h u := by
  exact LinearMap.extendOfNorm_eq
    (denseRange_subtype_val.mpr (lpInterL2_dense (p := p) hp))
    ⟨C, by
      exact lpInterL2Map_bound_subtype h⟩ u

theorem lpExtensionCore_norm_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C)
    (u : Lp ℝ p (volume : Measure Vec3)) :
    ‖lpExtensionCore hp h u‖ ≤ C * ‖u‖ := by
  change ‖((lpInterL2Map h).extendOfNorm (lpInterL2Submodule p).subtype) u‖ ≤ C * ‖u‖
  simpa only using
    (LinearMap.norm_extendOfNorm_apply_le
    (denseRange_subtype_val.mpr (lpInterL2_dense (p := p) hp))
    C (lpInterL2Map_bound_subtype h) u)

def lpExtensionRepresentative {p : ℝ≥0∞} [Fact (1 ≤ p)] {C : ℝ}
    (hp : p ≠ ∞) (h : LpExtensionInput p C) (f : Vec3 → ℝ) : Vec3 → ℝ := by
  classical
  exact if hf : MemLp f p volume then
    (Lp.aestronglyMeasurable (lpExtensionCore hp h (hf.toLp f))).aemeasurable.mk
      (lpExtensionCore hp h (hf.toLp f))
  else 0

theorem lpExtensionRepresentative_measurable {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C) {f : Vec3 → ℝ}
    (hf : MemLp f p volume) :
    Measurable (lpExtensionRepresentative hp h f) := by
  classical
  simp only [lpExtensionRepresentative, hf, ↓reduceDIte]
  exact (Lp.aestronglyMeasurable (lpExtensionCore hp h (hf.toLp f))).aemeasurable.measurable_mk

theorem lpExtensionRepresentative_ae_eq_core {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C) {f : Vec3 → ℝ}
    (hf : MemLp f p volume) :
    lpExtensionRepresentative hp h f =ᵐ[volume]
      lpExtensionCore hp h (hf.toLp f) := by
  classical
  simp only [lpExtensionRepresentative, hf, ↓reduceDIte]
  exact (Lp.aestronglyMeasurable (lpExtensionCore hp h (hf.toLp f))).aemeasurable.ae_eq_mk.symm

theorem lpExtensionRepresentative_memLp {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C) {f : Vec3 → ℝ}
    (hf : MemLp f p volume) :
    MemLp (lpExtensionRepresentative hp h f) p volume := by
  exact memLp_congr_ae (lpExtensionRepresentative_ae_eq_core hp h hf) |>.2
    (Lp.memLp (lpExtensionCore hp h (hf.toLp f)))

theorem lpExtensionRepresentative_toLp_eq_core {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C) {f : Vec3 → ℝ}
    (hf : MemLp f p volume) :
    (lpExtensionRepresentative_memLp hp h hf).toLp
      (lpExtensionRepresentative hp h f) = lpExtensionCore hp h (hf.toLp f) := by
  apply Lp.ext
  exact (lpExtensionRepresentative_memLp hp h hf).coeFn_toLp.trans
    (lpExtensionRepresentative_ae_eq_core hp h hf)

theorem lpExtensionRepresentative_norm_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C) {f : Vec3 → ℝ}
    (hf : MemLp f p volume) :
    ‖(lpExtensionRepresentative_memLp hp h hf).toLp
      (lpExtensionRepresentative hp h f)‖ ≤ C * ‖hf.toLp f‖ := by
  rw [lpExtensionRepresentative_toLp_eq_core hp h hf]
  exact lpExtensionCore_norm_le hp h _

def lpExtensionOperator {p : ℝ≥0∞} [Fact (1 ≤ p)] {C : ℝ}
    (hp : p ≠ ∞) (h : LpExtensionInput p C) (f : Vec3 → ℝ) : Vec3 → ℝ :=
  lpExtensionRepresentative hp h f

theorem lpExtensionOperator_memLp {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C) {f : Vec3 → ℝ}
    (hf : MemLp f p volume) :
    MemLp (lpExtensionOperator hp h f) p volume :=
  lpExtensionRepresentative_memLp hp h hf

theorem lpExtensionOperator_toLp_bound {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C) {f : Vec3 → ℝ}
    (hf : MemLp f p volume) :
    ‖(lpExtensionOperator_memLp hp h hf).toLp
        (lpExtensionOperator hp h f)‖ ≤ C * ‖hf.toLp f‖ :=
  lpExtensionRepresentative_norm_le hp h hf

def lpExtensionTensorOperator {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : Fin 3 → Fin 3 → ℝ} (hp : p ≠ ∞)
    (h : ∀ i j, LpExtensionInput p (C i j))
    (G : Fin 3 → Fin 3 → Vec3 → ℝ) : Vec3 → ℝ :=
  fun x => ∑ i, ∑ j, lpExtensionOperator hp (h i j) (G i j) x

theorem lpExtensionTensorOperator_memLp {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : Fin 3 → Fin 3 → ℝ} (hp : p ≠ ∞)
    (h : ∀ i j, LpExtensionInput p (C i j))
    {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) p volume) :
    MemLp (lpExtensionTensorOperator hp h G) p volume := by
  have hmem : ∀ i j, MemLp (lpExtensionOperator hp (h i j) (G i j)) p volume := by
    intro i j
    exact lpExtensionOperator_memLp hp (h i j) (hG i j)
  have hinner : ∀ i, MemLp (fun x =>
      ∑ j, lpExtensionOperator hp (h i j) (G i j) x) p volume := by
    intro i
    exact memLp_finsetSum Finset.univ (fun j _ => hmem i j)
  have houter := memLp_finsetSum Finset.univ (fun i _ => hinner i)
  change MemLp (fun x => ∑ i, ∑ j,
      lpExtensionOperator hp (h i j) (G i j) x) p volume
  exact houter

theorem lpExtensionTensorOperator_eLpNorm_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : Fin 3 → Fin 3 → ℝ} (hp : p ≠ ∞)
    (h : ∀ i j, LpExtensionInput p (C i j))
    (hC : ∀ i j, 0 ≤ C i j)
    {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) p volume)
    (_ : ∀ i j, HasCompactSupport (G i j))
    (hpone : (1 : ℝ≥0∞) ≤ p) :
    eLpNorm (lpExtensionTensorOperator hp h G) p volume ≤
      ∑ i, ∑ j, ENNReal.ofReal (C i j) * eLpNorm (G i j) p volume := by
  have hcomponent : ∀ i j, eLpNorm (lpExtensionOperator hp (h i j) (G i j))
      p volume ≤ ENNReal.ofReal (C i j) * eLpNorm (G i j) p volume := by
    intro i j
    exact CKN.Core.Endgame.eLpNorm_le_of_toLp_norm_le
      (hG i j) (lpExtensionOperator_memLp hp (h i j) (hG i j)) (hC i j)
      (lpExtensionOperator_toLp_bound hp (h i j) (hG i j))
  calc
    eLpNorm (lpExtensionTensorOperator hp h G) p volume ≤
        ∑ i, eLpNorm (fun x =>
          ∑ j, lpExtensionOperator hp (h i j) (G i j) x) p volume := by
      change eLpNorm (∑ i, fun x =>
        ∑ j, lpExtensionOperator hp (h i j) (G i j) x) p volume ≤ _
      exact eLpNorm_sum_le hpone
    _ ≤ ∑ i, ∑ j, eLpNorm (lpExtensionOperator hp (h i j) (G i j))
        p volume := by
      apply Finset.sum_le_sum
      intro i hi
      change eLpNorm (∑ j, lpExtensionOperator hp (h i j) (G i j)) p volume ≤ _
      exact eLpNorm_sum_le hpone
    _ ≤ ∑ i, ∑ j, ENNReal.ofReal (C i j) * eLpNorm (G i j) p volume := by
      exact Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hcomponent i j

def lpInterL2Input {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : Vec3 → ℝ}
    (hf : MemLp f p volume) (hf₂ : MemLp f (2 : ℝ≥0∞) volume) :
    lpInterL2Submodule p := by
  let hu₂ : MemLp (hf.toLp f : Vec3 → ℝ) (2 : ℝ≥0∞) volume :=
    memLp_congr_ae hf.coeFn_toLp |>.2 hf₂
  exact ⟨hf.toLp f, hu₂⟩

theorem lpExtensionRepresentative_ae_eq_T {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C) {f : Vec3 → ℝ}
    (hf : MemLp f p volume) (hf₂ : MemLp f (2 : ℝ≥0∞) volume) :
    lpExtensionRepresentative hp h f =ᵐ[volume] h.T f := by
  let u : lpInterL2Submodule p := lpInterL2Input hf hf₂
  have hu₂ : MemLp (u : Vec3 → ℝ) (2 : ℝ≥0∞) volume := by
    dsimp [u, lpInterL2Input]
    exact memLp_congr_ae hf.coeFn_toLp |>.2 hf₂
  have hu_eq : (u : Vec3 → ℝ) =ᵐ[volume] f := by
    simpa only [u, lpInterL2Input] using hf.coeFn_toLp
  have hmap : lpInterL2Map h u =ᵐ[volume] h.T (u : Vec3 → ℝ) :=
    by
      have hout : MemLp (h.T (u : Vec3 → ℝ)) p volume :=
        h.output_mem (Lp.memLp u.1) hu₂
      exact hout.coeFn_toLp
  calc
    lpExtensionRepresentative hp h f =ᵐ[volume] lpExtensionCore hp h (hf.toLp f) :=
      lpExtensionRepresentative_ae_eq_core hp h hf
    _ =ᵐ[volume] lpExtensionCore hp h u := by
      exact Filter.Eventually.of_forall (fun _ => rfl)
    _ =ᵐ[volume] lpInterL2Map h u := by
      exact Eventually.of_forall (fun x =>
        congrArg (fun q : Lp ℝ p volume => q x) (lpExtensionCore_agrees hp h u))
    _ =ᵐ[volume] h.T (u : Vec3 → ℝ) := hmap
    _ =ᵐ[volume] h.T f := h.congr_ae hu₂ hf₂ hu_eq

theorem lpExtensionRepresentative_add_ae {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C)
    {f g : Vec3 → ℝ} (hf : MemLp f p volume) (hg : MemLp g p volume) :
    lpExtensionRepresentative hp h (f + g) =ᵐ[volume]
      lpExtensionRepresentative hp h f + lpExtensionRepresentative hp h g := by
  have hfg : MemLp (f + g) p volume := hf.add hg
  have heq : lpExtensionCore hp h (hfg.toLp (f + g)) =
      lpExtensionCore hp h (hf.toLp f + hg.toLp g) := by
    congr 1
  calc
    lpExtensionRepresentative hp h (f + g) =ᵐ[volume]
        lpExtensionCore hp h (hfg.toLp (f + g)) :=
      lpExtensionRepresentative_ae_eq_core hp h hfg
    _ =ᵐ[volume] lpExtensionCore hp h (hf.toLp f + hg.toLp g) := by
      rw [heq]
    _ =ᵐ[volume]
        lpExtensionRepresentative hp h f + lpExtensionRepresentative hp h g := by
      rw [map_add]
      filter_upwards [Lp.coeFn_add (lpExtensionCore hp h (hf.toLp f))
          (lpExtensionCore hp h (hg.toLp g)),
        lpExtensionRepresentative_ae_eq_core hp h hf,
        lpExtensionRepresentative_ae_eq_core hp h hg] with x hsum hx hy
      calc
        (((lpExtensionCore hp h (hf.toLp f) +
          lpExtensionCore hp h (hg.toLp g)) : Lp ℝ p volume) : Vec3 → ℝ) x =
            ((lpExtensionCore hp h (hf.toLp f) : Vec3 → ℝ) +
              (lpExtensionCore hp h (hg.toLp g) : Vec3 → ℝ)) x := hsum
        _ =
            (lpExtensionCore hp h (hf.toLp f) : Vec3 → ℝ) x +
              (lpExtensionCore hp h (hg.toLp g) : Vec3 → ℝ) x := by rfl
        _ = lpExtensionRepresentative hp h f x +
            lpExtensionRepresentative hp h g x := by rw [← hx, ← hy]

theorem lpExtensionRepresentative_smul_ae {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C) (c : ℝ)
    {f : Vec3 → ℝ} (hf : MemLp f p volume) :
    lpExtensionRepresentative hp h (c • f) =ᵐ[volume]
      c • lpExtensionRepresentative hp h f := by
  have hcf : MemLp (c • f) p volume := hf.const_smul c
  have heq : lpExtensionCore hp h (hcf.toLp (c • f)) =
      lpExtensionCore hp h (c • hf.toLp f) := by
    congr 1
  calc
    lpExtensionRepresentative hp h (c • f) =ᵐ[volume]
        lpExtensionCore hp h (hcf.toLp (c • f)) :=
      lpExtensionRepresentative_ae_eq_core hp h hcf
    _ =ᵐ[volume] lpExtensionCore hp h (c • hf.toLp f) := by
      rw [heq]
    _ =ᵐ[volume] c • lpExtensionRepresentative hp h f := by
      rw [map_smul]
      filter_upwards [Lp.coeFn_smul c (lpExtensionCore hp h (hf.toLp f)),
        lpExtensionRepresentative_ae_eq_core hp h hf] with x hsm hx
      calc
        (((c • lpExtensionCore hp h (hf.toLp f)) : Lp ℝ p volume) : Vec3 → ℝ) x =
            (c • (lpExtensionCore hp h (hf.toLp f) : Vec3 → ℝ)) x := hsm
        _ =
            c • (lpExtensionCore hp h (hf.toLp f) : Vec3 → ℝ) x := by rfl
        _ = c • lpExtensionRepresentative hp h f x := by rw [← hx]
        _ = (c • lpExtensionRepresentative hp h f) x := by rfl

theorem lpExtensionRepresentative_congr_ae {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C)
    {f g : Vec3 → ℝ} (hf : MemLp f p volume) (hg : MemLp g p volume)
    (hfg : f =ᵐ[volume] g) :
    lpExtensionRepresentative hp h f =ᵐ[volume]
      lpExtensionRepresentative hp h g := by
  have hto : hf.toLp f = hg.toLp g := MemLp.toLp_congr hf hg hfg
  have hcore : lpExtensionCore hp h (hf.toLp f) =
      lpExtensionCore hp h (hg.toLp g) := by rw [hto]
  calc
    lpExtensionRepresentative hp h f =ᵐ[volume] lpExtensionCore hp h (hf.toLp f) :=
      lpExtensionRepresentative_ae_eq_core hp h hf
    _ =ᵐ[volume] lpExtensionCore hp h (hg.toLp g) := by rw [hcore]
    _ =ᵐ[volume] lpExtensionRepresentative hp h g :=
      (lpExtensionRepresentative_ae_eq_core hp h hg).symm

def lpPairingWith {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q]
    (g : Lp ℝ q (volume : Measure Vec3)) :
    Lp ℝ p (volume : Measure Vec3) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ g).comp
    (ContinuousLinearMap.lpPairing volume p q (ContinuousLinearMap.mul ℝ ℝ))

private lemma lpPairingWith_apply {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q]
    (g : Lp ℝ q (volume : Measure Vec3)) (f : Lp ℝ p (volume : Measure Vec3)) :
    lpPairingWith g f = ∫ x, f x * g x := by
  change (ContinuousLinearMap.lpPairing volume p q (ContinuousLinearMap.mul ℝ ℝ) f) g = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  rfl

theorem lpExtension_distribution_identity_transfer
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C)
    {lap rhs : Vec3 → ℝ} (hlap : MemLp lap q volume) (hrhs : MemLp rhs q volume)
    (s : Set (Lp ℝ p (volume : Measure Vec3))) (hs : Dense s)
    (_ : ∀ u ∈ s, HasCompactSupport (u : Vec3 → ℝ))
    (hs₂ : ∀ u ∈ s, MemLp (u : Vec3 → ℝ) (2 : ℝ≥0∞) volume)
    (hidentity : ∀ u ∈ s,
      ∫ x, h.T (u : Vec3 → ℝ) x * lap x = ∫ x, (u : Vec3 → ℝ) x * rhs x)
    {f : Vec3 → ℝ} (hf : MemLp f p volume) (_ : HasCompactSupport f) :
    ∫ x, lpExtensionRepresentative hp h f x * lap x =
      ∫ x, f x * rhs x := by
  let lapLp : Lp ℝ q (volume : Measure Vec3) := hlap.toLp lap
  let rhsLp : Lp ℝ q (volume : Measure Vec3) := hrhs.toLp rhs
  let left : Lp ℝ p (volume : Measure Vec3) →L[ℝ] ℝ :=
    (lpPairingWith (p := p) (q := q) lapLp).comp (lpExtensionCore hp h)
  let right : Lp ℝ p (volume : Measure Vec3) →L[ℝ] ℝ :=
    lpPairingWith (p := p) (q := q) rhsLp
  have hEq : left = right := by
    apply ContinuousLinearMap.ext
    intro u
    have hfun : (fun v : Lp ℝ p (volume : Measure Vec3) => left v) =
        (fun v => right v) := by
      apply Continuous.ext_on hs
        left.continuous right.continuous
      intro v hv
      have hv₂ : MemLp (v : Vec3 → ℝ) (2 : ℝ≥0∞) volume := hs₂ v hv
      let u : lpInterL2Submodule p := ⟨v, hv₂⟩
      have hTae : h.T (v : Vec3 → ℝ) =ᵐ[volume]
          (lpInterL2Map h u : Vec3 → ℝ) :=
            (h.output_mem (Lp.memLp v) hv₂).coeFn_toLp.symm
      have hcore := lpExtensionCore_agrees hp h u
      have hleft : left v = ∫ x, h.T (v : Vec3 → ℝ) x * lap x := by
        change (lpPairingWith lapLp) (lpExtensionCore hp h v) = _
        rw [lpPairingWith_apply]
        rw [show lpExtensionCore hp h v = lpInterL2Map h u from hcore]
        apply integral_congr_ae
        filter_upwards [hTae, hlap.coeFn_toLp] with x hx hy
        rw [← hx, hy]
      have hright : right v = ∫ x, (v : Vec3 → ℝ) x * rhs x := by
        change (lpPairingWith rhsLp) v = _
        rw [lpPairingWith_apply]
        apply integral_congr_ae
        filter_upwards [hrhs.coeFn_toLp] with x hx
        rw [hx]
      rw [hleft, hright]
      exact hidentity v hv
    exact congrFun hfun u
  have hpair : left (hf.toLp f) = right (hf.toLp f) := by rw [hEq]
  have hpair' : (lpPairingWith lapLp) (lpExtensionCore hp h (hf.toLp f)) =
      (lpPairingWith rhsLp) (hf.toLp f) := hpair
  have hrep : lpExtensionRepresentative hp h f =ᵐ[volume]
      (lpExtensionCore hp h (hf.toLp f) : Vec3 → ℝ) :=
    lpExtensionRepresentative_ae_eq_core hp h hf
  calc
    ∫ x, lpExtensionRepresentative hp h f x * lap x =
        ∫ x, (lpExtensionCore hp h (hf.toLp f) : Vec3 → ℝ) x * lap x := by
      apply integral_congr_ae
      filter_upwards [hrep] with x hx
      rw [hx]
    _ = (lpPairingWith lapLp) (lpExtensionCore hp h (hf.toLp f)) := by
      rw [lpPairingWith_apply]
      apply integral_congr_ae
      filter_upwards [hlap.coeFn_toLp] with x hx
      rw [hx]
    _ = (lpPairingWith rhsLp) (hf.toLp f) := hpair'
    _ = ∫ x, (hf.toLp f : Vec3 → ℝ) x * rhs x := by
      rw [lpPairingWith_apply]
      apply integral_congr_ae
      filter_upwards [hrhs.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x, f x * rhs x := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]

theorem lpExtensionTensorOperator_distributional_pairing
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q]
    {C : Fin 3 → Fin 3 → ℝ} (hp : p ≠ ∞)
    (h : ∀ i j, LpExtensionInput p (C i j))
    {lap : Vec3 → ℝ} (hlap : MemLp lap q volume)
    {rhs : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hrhs : ∀ i j, MemLp (rhs i j) q volume)
    (s : Set (Lp ℝ p (volume : Measure Vec3))) (hs : Dense s)
    (hs_compact : ∀ u ∈ s, HasCompactSupport (u : Vec3 → ℝ))
    (hs₂ : ∀ u ∈ s, MemLp (u : Vec3 → ℝ) (2 : ℝ≥0∞) volume)
    (hidentity : ∀ i j u, u ∈ s →
      ∫ x, (h i j).T (u : Vec3 → ℝ) x * lap x =
        ∫ x, (u : Vec3 → ℝ) x * rhs i j x)
    {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) p volume)
    (hGc : ∀ i j, HasCompactSupport (G i j)) :
    ∫ x, lpExtensionTensorOperator hp h G x * lap x =
      ∫ x, ∑ i, ∑ j, G i j x * rhs i j x := by
  have hpair : ∀ i j, ∫ x, lpExtensionOperator hp (h i j) (G i j) x * lap x =
      ∫ x, G i j x * rhs i j x := by
    intro i j
    exact lpExtension_distribution_identity_transfer hp (h i j) hlap (hrhs i j)
      s hs hs_compact hs₂ (fun u hu => hidentity i j u hu) (hG i j) (hGc i j)
  have hleft : ∀ i j, Integrable
      (fun x => lpExtensionOperator hp (h i j) (G i j) x * lap x) volume := by
    intro i j
    exact (lpExtensionOperator_memLp hp (h i j) (hG i j)).integrable_mul hlap
  have hright : ∀ i j, Integrable
      (fun x => G i j x * rhs i j x) volume := by
    intro i j
    exact (hG i j).integrable_mul (hrhs i j)
  have hleft_inner : ∀ i, ∫ x, ∑ j,
      lpExtensionOperator hp (h i j) (G i j) x * lap x =
      ∑ j, ∫ x, lpExtensionOperator hp (h i j) (G i j) x * lap x := by
    intro i
    rw [integral_finsetSum]
    intro j hj
    exact hleft i j
  have hright_inner : ∀ i, ∫ x, ∑ j, G i j x * rhs i j x =
      ∑ j, ∫ x, G i j x * rhs i j x := by
    intro i
    rw [integral_finsetSum]
    intro j hj
    exact hright i j
  have hleft_outer : ∫ x, ∑ i, ∑ j,
      lpExtensionOperator hp (h i j) (G i j) x * lap x =
      ∑ i, ∫ x, ∑ j,
        lpExtensionOperator hp (h i j) (G i j) x * lap x := by
    rw [integral_finsetSum]
    intro i hi
    exact integrable_finsetSum Finset.univ (fun j hj => hleft i j)
  have hright_outer : ∫ x, ∑ i, ∑ j, G i j x * rhs i j x =
      ∑ i, ∫ x, ∑ j, G i j x * rhs i j x := by
    rw [integral_finsetSum]
    intro i hi
    exact integrable_finsetSum Finset.univ (fun j hj => hright i j)
  unfold lpExtensionTensorOperator
  calc
    ∫ x, (∑ i, ∑ j, lpExtensionOperator hp (h i j) (G i j) x) * lap x =
        ∫ x, ∑ i, ∑ j,
          lpExtensionOperator hp (h i j) (G i j) x * lap x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Finset.sum_mul]
      congr 1
      funext i
      rw [Finset.sum_mul]
    _ = ∑ i, ∫ x, ∑ j,
        lpExtensionOperator hp (h i j) (G i j) x * lap x := hleft_outer
    _ = ∑ i, ∑ j, ∫ x,
        lpExtensionOperator hp (h i j) (G i j) x * lap x := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hleft_inner i
    _ = ∑ i, ∑ j, ∫ x, G i j x * rhs i j x := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hpair i j
    _ = ∑ i, ∫ x, ∑ j, G i j x * rhs i j x := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hright_inner i).symm
    _ = ∫ x, ∑ i, ∑ j, G i j x * rhs i j x := hright_outer.symm

theorem lpExtensionTensorOperator_agrees_exterior
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {C : Fin 3 → Fin 3 → ℝ}
    (hp : p ≠ ∞) (h : ∀ i j, LpExtensionInput p (C i j))
    {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    {L : Fin 3 → Fin 3 → (Vec3 → ℝ) → Vec3 → ℝ}
    (hExterior : ∀ i j x, x ∉ tsupport (G i j) →
      lpExtensionOperator hp (h i j) (G i j) x = L i j (G i j) x) :
    ∀ x, (∀ i j, x ∉ tsupport (G i j)) →
      lpExtensionTensorOperator hp h G x = ∑ i, ∑ j, L i j (G i j) x := by
  intro x hx
  simp only [lpExtensionTensorOperator]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact hExterior i j x (hx i j)

theorem lpExtensionRepresentative_bound {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C) {f : Vec3 → ℝ}
    (hf : MemLp f p volume) :
    ‖lpExtensionCore hp h (hf.toLp f)‖ ≤ C * ‖hf.toLp f‖ :=
  lpExtensionCore_norm_le hp h _

end CKN.Foundation.Euclidean
