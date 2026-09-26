/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondWeakAssembly
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpDensity

/-!
# Riesz Second Weak Countable

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

private lemma finite_bad_sum_memLp_two_countable
    {F : Vec3 → ℝ} {level : ℝ} (D : CZDecomposition F level)
    (hF₂ : MemLp F (2 : ℝ≥0∞) volume)
    {ι : Type*} (s : Finset ι)
    (q : ι → {Q // Q ∈ D.cubes}) :
    MemLp (fun x => ∑ k ∈ s, dyadicBadPart F (q k).1 x)
      (2 : ℝ≥0∞) volume := by
  classical
  apply memLp_finsetSum
  intro k hk
  exact dyadic_bad_part_memLp_two D hF₂ (q k)

private lemma bad_partial_pointwise_limit
    {F : Vec3 → ℝ} {level : ℝ} (D : CZDecomposition F level)
    {e : ℕ ≃ {Q // Q ∈ D.cubes}} :
    ∀ᵐ x ∂volume, Tendsto
      (fun n => ∑ k ∈ Finset.range n, dyadicBadPart F (e k).1 x)
        atTop (𝓝 (F x - dyadicGoodPart F D.cubes x)) := by
  have hdecomp := dyadic_good_bad_decomposition_ae D
  filter_upwards [hdecomp] with x hx
  by_cases hmem : dyadicCubeMember D.cubes x
  · obtain ⟨Q, hQ, hQx⟩ := hmem
    have hmem' : dyadicCubeMember D.cubes x := ⟨Q, hQ, hQx⟩
    let q : {Q // Q ∈ D.cubes} := ⟨Q, hQ⟩
    obtain ⟨k, hk⟩ := e.surjective q
    have hzero : ∀ r : {Q // Q ∈ D.cubes}, r ≠ q →
        dyadicBadPart F r.1 x = 0 := by
      intro r hr
      have hxr : x ∉ dyadicCubeSet r.1 := by
        intro hxr
        exact (Set.disjoint_left.1
          (D.cubes_pairwise_disjoint r.2 q.2
            (Subtype.coe_ne_coe.mpr hr))) hxr hQx
      exact Set.indicator_of_notMem hxr _
    have hsum : ∑' r : {Q // Q ∈ D.cubes},
        dyadicBadPart F r.1 x = dyadicBadPart F q.1 x := by
      rw [tsum_eq_single q]
      intro r hr
      exact hzero r hr
    have htail : ∀ᶠ n : ℕ in atTop,
        (∑ k' ∈ Finset.range n, dyadicBadPart F (e k').1 x) =
          dyadicBadPart F q.1 x := by
      filter_upwards [eventually_ge_atTop (k + 1)] with n hn
      have hkn : k ∈ Finset.range n := Finset.mem_range.mpr (lt_of_lt_of_le
        (Nat.lt_succ_self k) hn)
      rw [Finset.sum_eq_single k]
      · rw [hk]
      · intro k' hk' hne
        apply hzero
        intro heq
        apply hne
        exact e.injective (heq.trans hk.symm)
      · intro hnot
        exact False.elim (hnot hkn)
    have hlimit :
        Tendsto (fun n => ∑ k ∈ Finset.range n,
          dyadicBadPart F (e k).1 x) atTop (𝓝 (dyadicBadPart F q.1 x)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => dyadicBadPart F q.1 x)
        atTop (𝓝 (dyadicBadPart F q.1 x))).congr' (by
          filter_upwards [htail] with n hn
          exact hn.symm)
    have hgood : dyadicGoodPart F D.cubes x = dyadicAverage F Q := by
      simp only [dyadicGoodPart, dite_eq_left hmem']
      have hchoose : Classical.choose hmem' = Q := by
        by_contra hne
        exact (Set.disjoint_left.1
          (D.cubes_pairwise_disjoint (Classical.choose_spec hmem').1
            hQ hne)) (Classical.choose_spec hmem').2 hQx
      rw [hchoose]
    have hbad : dyadicBadPart F q.1 x = F x - dyadicAverage F Q := by
      rw [dyadicBadPart, Set.indicator_of_mem hQx]
    have hdiff : F x - dyadicGoodPart F D.cubes x =
        dyadicBadPart F q.1 x := by
      rw [hgood, hbad]
    rw [hdiff]
    exact hlimit
  · have hzero : ∀ r : {Q // Q ∈ D.cubes},
        dyadicBadPart F r.1 x = 0 := by
      intro r
      apply Set.indicator_of_notMem
      intro hxr
      exact hmem ⟨r.1, r.2, hxr⟩
    have hsum : ∀ n : ℕ, (∑ k ∈ Finset.range n,
        dyadicBadPart F (e k).1 x) = 0 := by
      intro n
      apply Finset.sum_eq_zero
      intro k hk
      exact hzero (e k)
    have hFgood : F x - dyadicGoodPart F D.cubes x = 0 := by
      have hgood : dyadicGoodPart F D.cubes x = F x := by
        simp only [dyadicGoodPart, dite_eq_right hmem]
      rw [hgood]
      ring
    rw [hFgood]
    rw [show (fun n => ∑ k ∈ Finset.range n,
        dyadicBadPart F (e k).1 x) = fun _ => 0 by
      funext n
      exact hsum n]
    exact tendsto_const_nhds

private lemma bad_partial_eLpNorm_tendsto_zero_countable
    {F : Vec3 → ℝ} {level : ℝ} (D : CZDecomposition F level)
    (hF₂ : MemLp F (2 : ℝ≥0∞) volume)
    {e : ℕ ≃ {Q // Q ∈ D.cubes}} :
    Tendsto (fun n => eLpNorm
      ((fun x => ∑ k ∈ Finset.range n,
        dyadicBadPart F (e k).1 x) -
        (fun x => F x - dyadicGoodPart F D.cubes x))
      (2 : ℝ≥0∞) volume) atTop (𝓝 0) := by
  let H : Vec3 → ℝ := fun x => F x - dyadicGoodPart F D.cubes x
  let S : ℕ → Vec3 → ℝ := fun n x => ∑ k ∈ Finset.range n,
    dyadicBadPart F (e k).1 x
  have hH : MemLp H (2 : ℝ≥0∞) volume := by
    simpa only [H] using dyadic_bad_sum_memLp_two D hF₂
  have hS : ∀ n, MemLp (S n) (2 : ℝ≥0∞) volume := by
    intro n
    exact finite_bad_sum_memLp_two_countable D hF₂ (Finset.range n) e
  have hpoint : ∀ᵐ x ∂volume, Tendsto (fun n => S n x)
      atTop (𝓝 (H x)) := by
    simpa only [S, H] using bad_partial_pointwise_limit D
  have hmeas : ∀ n, AEMeasurable
      (fun x => ENNReal.ofReal |S n x - H x| ^ (2 : ℝ)) volume := by
    intro n
    have hmeas0 : AEMeasurable (fun x => |S n x - H x|) volume :=
      ((hS n).aestronglyMeasurable.sub hH.aestronglyMeasurable).norm.aemeasurable
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      hmeas0.ennreal_ofReal
  have hbound : ∀ n, (fun x => ENNReal.ofReal |S n x - H x| ^ (2 : ℝ)) ≤ᵐ[volume]
      (fun x => 4 * (ENNReal.ofReal |H x|) ^ (2 : ℝ)) := by
    have hdecomp := dyadic_good_bad_decomposition_ae D
    intro n
    filter_upwards [hdecomp] with x hx
    by_cases hmem : dyadicCubeMember D.cubes x
    · obtain ⟨Q, hQ, hQx⟩ := hmem
      let q : {Q // Q ∈ D.cubes} := ⟨Q, hQ⟩
      obtain ⟨k, hk⟩ := e.surjective q
      have hzero : ∀ r : {Q // Q ∈ D.cubes}, r ≠ q →
          dyadicBadPart F r.1 x = 0 := by
        intro r hr
        have hxr : x ∉ dyadicCubeSet r.1 := by
          intro hxr
          exact (Set.disjoint_left.1
            (D.cubes_pairwise_disjoint r.2 q.2
              (Subtype.coe_ne_coe.mpr hr))) hxr hQx
        exact Set.indicator_of_notMem hxr _
      have hsum : ∑' r : {Q // Q ∈ D.cubes},
          dyadicBadPart F r.1 x = dyadicBadPart F q.1 x := by
        rw [tsum_eq_single q]
        intro r hr
        exact hzero r hr
      have hHq : H x = dyadicBadPart F q.1 x := by
        dsimp [H]
        rw [hx, hsum]
        ring
      by_cases hkn : k ∈ Finset.range n
      · have hSkn : S n x = dyadicBadPart F q.1 x := by
          dsimp [S]
          rw [Finset.sum_eq_single k]
          · rw [hk]
          · intro k' hk' hne
            apply hzero
            intro heq
            apply hne
            exact e.injective (heq.trans hk.symm)
          · intro hnot
            exact False.elim (hnot hkn)
        rw [hHq, hSkn]
        simp
      · have hSn_zero : S n x = 0 := by
          dsimp [S]
          apply Finset.sum_eq_zero
          intro k' hk'
          apply hzero
          intro heq
          apply hkn
          have hEq : k' = k := e.injective (heq.trans hk.symm)
          rw [← hEq]
          exact hk'
        rw [hSn_zero]
        rw [zero_sub, abs_neg]
        calc
          ENNReal.ofReal |H x| ^ (2 : ℝ) =
              1 * (ENNReal.ofReal |H x| ^ (2 : ℝ)) := by simp
          _ ≤ 4 * (ENNReal.ofReal |H x| ^ (2 : ℝ)) := by
            exact mul_le_mul_left (by norm_num) _
    · have hSn_zero : ∀ n, S n x = 0 := by
        intro n
        dsimp [S]
        apply Finset.sum_eq_zero
        intro k hk
        apply Set.indicator_of_notMem
        intro hQx
        exact hmem ⟨(e k).1, (e k).2, hQx⟩
      have hHx : H x = 0 := by
        dsimp [H]
        rw [hx]
        have hz : ∀ r : {Q // Q ∈ D.cubes},
            dyadicBadPart F r.1 x = 0 := by
          intro r
          apply Set.indicator_of_notMem
          intro hQx
          exact hmem ⟨r.1, r.2, hQx⟩
        have htsum : ∑' r : {Q // Q ∈ D.cubes},
            dyadicBadPart F r.1 x = 0 := by
          have hz' : (fun r : {Q // Q ∈ D.cubes} =>
              dyadicBadPart F r.1 x) = fun _ => 0 := by
            funext r
            exact hz r
          rw [hz']
          simp
        rw [htsum]
        ring
      rw [hSn_zero n, hHx]
      simp
  have hdom : Integrable (fun x => 4 * |H x| ^ (2 : ℝ)) volume := by
    convert hH.integrable_sq.const_mul 4 using 1
    funext x
    norm_num [Real.rpow_natCast, sq_abs]
  have hdomtop' : (∫⁻ x, ENNReal.ofReal (4 * |H x| ^ (2 : ℝ))) < ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hdom
      (ae_of_all _ (fun x => by positivity))]
    exact ENNReal.ofReal_lt_top
  have hdomtop : (∫⁻ x, 4 * (ENNReal.ofReal |H x|) ^ (2 : ℝ)) < ∞ := by
    calc
      (∫⁻ x, 4 * (ENNReal.ofReal |H x|) ^ (2 : ℝ)) =
          ∫⁻ x, ENNReal.ofReal (4 * |H x| ^ (2 : ℝ)) := by
        apply lintegral_congr
        intro x
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg
          (abs_nonneg _)]
        on_goal 1 => norm_num
        positivity
      _ < ∞ := hdomtop'
  have hlim : ∀ᵐ x ∂volume, Tendsto
      (fun n => ENNReal.ofReal |S n x - H x| ^ (2 : ℝ)) atTop (𝓝 0) := by
    filter_upwards [hpoint] with x hx
    have hsub : Tendsto (fun n => S n x - H x) atTop (𝓝 0) := by
      simpa only [sub_self] using hx.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => H x) atTop (𝓝 (H x)))
    have habs : Tendsto (fun n => |S n x - H x|) atTop (𝓝 0) := by
      change Tendsto (abs ∘ (fun n => S n x - H x)) atTop (𝓝 0)
      convert continuous_abs.continuousAt.tendsto.comp hsub using 1; simp
    have hpow : Tendsto (fun n => |S n x - H x| ^ (2 : ℝ)) atTop (𝓝 0) := by
      convert habs.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 2)) using 1;
        norm_num
    have hof : Tendsto (fun n => ENNReal.ofReal
        |S n x - H x|) atTop (𝓝 0) :=
      by
        change Tendsto (ENNReal.ofReal ∘ (fun n => |S n x - H x|))
          atTop (𝓝 0)
        simpa only [ENNReal.ofReal_zero] using
          ENNReal.continuous_ofReal.continuousAt.tendsto.comp habs
    convert hof.ennrpow_const (2 : ℝ) using 1; norm_num
  have hI : Tendsto (fun n => ∫⁻ x,
      ENNReal.ofReal |S n x - H x| ^ (2 : ℝ)) atTop (𝓝 0) := by
    simpa only [lintegral_zero] using
      (tendsto_lintegral_of_dominated_convergence'
        (fun x => 4 * (ENNReal.ofReal |H x|) ^ (2 : ℝ)) hmeas hbound
        hdomtop.ne hlim)
  have hpow : ∀ n, (∫⁻ x, ENNReal.ofReal |S n x - H x| ^ (2 : ℝ)) =
      (eLpNorm (S n - H) (2 : ℝ≥0∞) volume) ^ (2 : ℝ) := by
    intro n
    have hp := lintegral_rpow_enorm_eq_rpow_eLpNorm'
      (f := S n - H) (μ := volume) (q := (2 : ℝ)) (by norm_num)
    have hmeas' := (hS n).aestronglyMeasurable.sub hH.aestronglyMeasurable
    have heq := eLpNorm_eq_eLpNorm' (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) hmeas'
    have heq' : eLpNorm (S n - H) (2 : ℝ≥0∞) volume =
        eLpNorm' (S n - H) (2 : ℝ) volume := by
      simpa only [show ENNReal.toReal (2 : ℝ≥0∞) = (2 : ℝ) by norm_num] using heq
    simpa only [Pi.sub_apply, absE, Real.enorm_eq_ofReal_abs, heq'] using hp
  have hroot : Tendsto (fun n =>
      ((∫⁻ x, ENNReal.ofReal |S n x - H x| ^ (2 : ℝ)) : ℝ≥0∞) ^
        (1 / (2 : ℝ))) atTop (𝓝 0) := by
    simpa using hI.ennrpow_const (1 / (2 : ℝ))
  have hnorm : Tendsto (fun n => eLpNorm (S n - H)
      (2 : ℝ≥0∞) volume) atTop (𝓝 0) := by
    convert hroot using 1
    funext n
    rw [hpow n, ← ENNReal.rpow_mul]
    norm_num
  simpa only [S, H] using hnorm

private lemma operator_finset_bad_sum_ae_countable
    {i j : Fin 3} (hL2 : RieszSecondL2Input i j)
    {F : Vec3 → ℝ} {level : ℝ} (D : CZDecomposition F level)
    (hF₂ : MemLp F (2 : ℝ≥0∞) volume)
    {ι : Type*} (s : Finset ι)
    (q : ι → {Q // Q ∈ D.cubes}) :
    rieszSecondL2MeasurableOperator hL2
        (MemLp.toLp
          (fun x => ∑ k ∈ s, dyadicBadPart F (q k).1 x)
          (finite_bad_sum_memLp_two_countable D hF₂ s q)) =ᵐ[volume]
      (fun x => ∑ k ∈ s,
        rieszSecondL2MeasurableOperator hL2
          (MemLp.toLp (dyadicBadPart F (q k).1)
            (dyadic_bad_part_memLp_two D hF₂ (q k))) x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero : MemLp (0 : Vec3 → ℝ) (2 : ℝ≥0∞) volume := by
        exact MemLp.zero
      have hsmul := rieszSecondL2MeasurableOperator_smul_ae hL2 (0 : ℝ)
        (MemLp.toLp (0 : Vec3 → ℝ) hzero)
      have htoLp : (MemLp.toLp
          (fun x => ∑ k ∈ (∅ : Finset ι), dyadicBadPart F (q k).1 x)
          (finite_bad_sum_memLp_two_countable D hF₂ ∅ q) : rieszSecondL2) =
          MemLp.toLp (0 : Vec3 → ℝ) hzero := by
        apply MemLp.toLp_congr
        filter_upwards [] with x
        simp
      rw [htoLp, MemLp.toLp_zero]
      convert hsmul using 1
      · simp
      · funext x
        simp
  | @insert a s ha ih =>
      let u : Vec3 → ℝ := fun x => ∑ k ∈ s, dyadicBadPart F (q k).1 x
      let v : Vec3 → ℝ := dyadicBadPart F (q a).1
      have hu : MemLp u (2 : ℝ≥0∞) volume := by
        simpa only [u] using finite_bad_sum_memLp_two_countable D hF₂ s q
      have hv : MemLp v (2 : ℝ≥0∞) volume :=
        dyadic_bad_part_memLp_two D hF₂ (q a)
      have huv : MemLp (u + v) (2 : ℝ≥0∞) volume := hu.add hv
      have htoLp : (huv.toLp (u + v) : rieszSecondL2) =
          hu.toLp u + hv.toLp v := MemLp.toLp_add hu hv
      have hadd := rieszSecondL2MeasurableOperator_add_ae hL2
        (hu.toLp u) (hv.toLp v)
      have hsumEq : (fun x => ∑ k ∈ insert a s,
          dyadicBadPart F (q k).1 x) = u + v := by
        funext x
        simp [Finset.sum_insert, ha, u, v, Pi.add_apply]
        ring
      have hmemInsert := finite_bad_sum_memLp_two_countable D hF₂
        (insert a s) q
      have htoLp' : (hmemInsert.toLp
          (fun x => ∑ k ∈ insert a s, dyadicBadPart F (q k).1 x) : rieszSecondL2) =
          hu.toLp u + hv.toLp v := by
        calc
          hmemInsert.toLp
              (fun x => ∑ k ∈ insert a s, dyadicBadPart F (q k).1 x) =
              huv.toLp (u + v) := by
                apply MemLp.toLp_congr hmemInsert huv
                filter_upwards [] with x
                exact congrFun hsumEq x
          _ = hu.toLp u + hv.toLp v := MemLp.toLp_add hu hv
      rw [htoLp']
      have huEq : hu.toLp u =
          MemLp.toLp (fun x => ∑ k ∈ s, dyadicBadPart F (q k).1 x)
            (finite_bad_sum_memLp_two_countable D hF₂ s q) := by
        apply MemLp.toLp_congr
        filter_upwards [] with x
        rfl
      have hxi' : rieszSecondL2MeasurableOperator hL2 (hu.toLp u) =ᵐ[volume]
          (fun x => ∑ k ∈ s,
            rieszSecondL2MeasurableOperator hL2
              (MemLp.toLp (dyadicBadPart F (q k).1)
                (dyadic_bad_part_memLp_two D hF₂ (q k))) x) := by
        rw [huEq]
        exact ih
      filter_upwards [hadd, hxi'] with x hxadd hxi
      rw [hxadd, Pi.add_apply, hxi]
      simp [Finset.sum_insert, ha]
      ring

private lemma measurableSet_rieszSecondCubeStar_countable (Q : DyadicIndex) :
    MeasurableSet (rieszSecondCubeStar Q) := by
  have hc : Continuous (fun x : Vec3 =>
      vec3EuclideanNorm (x - dyadicCubeCenter Q.scale Q.corner)) := by
    unfold vec3EuclideanNorm
    fun_prop
  exact (isClosed_Iic.preimage hc).measurableSet

private lemma rieszSecond_countable_bad_additivity_infinite_hsumstar_1 :
    ∀ {i j : Fin 3} (hL2 : Foundation.Euclidean.RieszSecondL2Input i j) {F : Vec3 → ℝ} {level : ℝ}
      (D : Foundation.Euclidean.CZDecomposition F level)
      (hF₂ : MemLp (m0 := MeasureSpace.toMeasurableSpace) F 2 volume) {C_H : ℝ≥0∞},
      (∀ (Q : { Q : Foundation.Euclidean.DyadicIndex // Q ∈ D.cubes }),
          ∫⁻ (x : Vec3) in (Foundation.Euclidean.rieszSecondCubeStar ↑Q)ᶜ,
              ENNReal.ofReal
                |Foundation.Euclidean.rieszSecondL2MeasurableOperator hL2
                    (MemLp.toLp (Foundation.Euclidean.dyadicBadPart F ↑Q)
                      (Foundation.Euclidean.dyadic_bad_part_memLp_two D hF₂ Q))
                    x| ≤
            C_H *
              ∫⁻ (x : Vec3) in Foundation.Euclidean.dyadicCubeSet ↑Q,
                ENNReal.ofReal |Foundation.Euclidean.dyadicBadPart F (↑Q) x|) →
        let b : { Q : Foundation.Euclidean.DyadicIndex // Q ∈ D.cubes } → Vec3 → ℝ := fun Q =>
          Foundation.Euclidean.dyadicBadPart F ↑Q;
        let Tbad : { Q : Foundation.Euclidean.DyadicIndex // Q ∈ D.cubes } → Vec3 → ℝ := fun Q =>
          Foundation.Euclidean.rieszSecondL2MeasurableOperator hL2
            (MemLp.toLp (b Q) (Foundation.Euclidean.dyadic_bad_part_memLp_two D hF₂ Q));
        ∑' (Q : { Q : Foundation.Euclidean.DyadicIndex // Q ∈ D.cubes }),
            ∫⁻ (x : Vec3) in (Foundation.Euclidean.rieszSecondCubeStar ↑Q)ᶜ,
              ENNReal.ofReal |Tbad Q x| ≤
          C_H * (2 * Foundation.Euclidean.dyadicL1Norm F)
    := by
  intro i j hL2 F level D hF₂ C_H hbridge b Tbad
  calc
    (∑' Q : {Q // Q ∈ D.cubes},
        ∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
          ENNReal.ofReal |Tbad Q x|) ≤
        ∑' Q : {Q // Q ∈ D.cubes}, C_H *
          ∫⁻ x in dyadicCubeSet Q.1,
            ENNReal.ofReal |dyadicBadPart F Q.1 x| := by
      apply ENNReal.tsum_le_tsum
      intro Q
      exact hbridge Q
    _ = C_H * (∑' Q : {Q // Q ∈ D.cubes},
        ∫⁻ x in dyadicCubeSet Q.1,
          ENNReal.ofReal |dyadicBadPart F Q.1 x|) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ C_H * (2 * dyadicL1Norm F) := by
      gcongr
      exact D.bad_part_l1_sum_le

private lemma rieszSecond_countable_bad_additivity_infinite_hinput_2 :
    ∀ {F : Vec3 → ℝ} {level : ℝ} (D : Foundation.Euclidean.CZDecomposition F level)
      [Infinite { Q : Foundation.Euclidean.DyadicIndex // Q ∈ D.cubes }],
      let H : Vec3 → ℝ := fun x => F x - Foundation.Euclidean.dyadicGoodPart F D.cubes x;
      let b : { Q : Foundation.Euclidean.DyadicIndex // Q ∈ D.cubes } → Vec3 → ℝ := fun Q =>
        Foundation.Euclidean.dyadicBadPart F ↑Q;
      ∀ (hHmem : MemLp (m0 := MeasureSpace.toMeasurableSpace) H 2 volume),
        let uH : ↥Foundation.Euclidean.rieszSecondL2 := MemLp.toLp H hHmem;
        let e : ℕ ≃ { Q : Foundation.Euclidean.DyadicIndex // Q ∈ D.cubes } :=
          Classical.choice nonempty_equiv_of_countable;
        let S : ℕ → Vec3 → ℝ := fun n x => ∑ k ∈ Finset.range n, b (e k) x;
        ∀ (hS : ∀ (n : ℕ), MemLp (m0 := MeasureSpace.toMeasurableSpace) (S n) 2 volume),
          let uₙ : ℕ → ↥Foundation.Euclidean.rieszSecondL2 := fun n => MemLp.toLp (S n) (hS n);
          Tendsto
              (fun (n : ℕ) => @eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace (S n - H) 2 volume)
              atTop (𝓝 0) →
            Tendsto
              (fun (n : ℕ) =>
                @eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace (↑↑(uₙ n - uH)) 2 volume)
              atTop (𝓝 0)
    := by
  intro F level D localHypothesis3 H b hHmem uH e S hS uₙ hpartial'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpartial'
  · intro n
    exact bot_le
  · intro n
    have hdiffmem : MemLp (S n - H) (2 : ℝ≥0∞) volume := (hS n).sub hHmem
    have hdiff : MemLp.toLp (S n - H) hdiffmem =
        uₙ n - uH := by
      simpa [uₙ, uH] using MemLp.toLp_sub (hS n) hHmem
    calc
      eLpNorm (uₙ n - uH)
          (2 : ℝ≥0∞) volume =
          eLpNorm (MemLp.toLp (S n - H) hdiffmem)
            (2 : ℝ≥0∞) volume := by rw [hdiff]
      _ = eLpNorm (S n - H) (2 : ℝ≥0∞) volume :=
        eLpNorm_congr_ae (MemLp.coeFn_toLp hdiffmem)
      _ ≤ (fun n => eLpNorm (S n - H)
          (2 : ℝ≥0∞) volume) n := by rfl

private lemma rieszSecond_countable_bad_additivity_infinite_hTout_3 :
    ∀ {i j : Fin 3} (hL2 : Foundation.Euclidean.RieszSecondL2Input i j) {F : Vec3 → ℝ} {level : ℝ}
      (D : Foundation.Euclidean.CZDecomposition F level)
      [Infinite { Q : Foundation.Euclidean.DyadicIndex // Q ∈ D.cubes }],
      let H : Vec3 → ℝ := fun x => F x - Foundation.Euclidean.dyadicGoodPart F D.cubes x;
      let b : { Q : Foundation.Euclidean.DyadicIndex // Q ∈ D.cubes } → Vec3 → ℝ := fun Q =>
        Foundation.Euclidean.dyadicBadPart F ↑Q;
      ∀ (hHmem : MemLp (m0 := MeasureSpace.toMeasurableSpace) H 2 volume),
        let uH : ↥Foundation.Euclidean.rieszSecondL2 := MemLp.toLp H hHmem;
        let e : ℕ ≃ { Q : Foundation.Euclidean.DyadicIndex // Q ∈ D.cubes } :=
          Classical.choice nonempty_equiv_of_countable;
        let S : ℕ → Vec3 → ℝ := fun n x => ∑ k ∈ Finset.range n, b (e k) x;
        ∀ (hS : ∀ (n : ℕ), MemLp (m0 := MeasureSpace.toMeasurableSpace) (S n) 2 volume),
          let uₙ : ℕ → ↥Foundation.Euclidean.rieszSecondL2 := fun n => MemLp.toLp (S n) (hS n);
          Tendsto
              (fun (n : ℕ) =>
                @eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace (↑↑(uₙ n - uH)) 2 volume)
              atTop (𝓝 0) →
            Tendsto
              (fun (n : ℕ) =>
                @eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace
                  (Foundation.Euclidean.rieszSecondL2MeasurableOperator hL2 (uₙ n) -
                    Foundation.Euclidean.rieszSecondL2MeasurableOperator hL2 uH)
                  2 volume)
              atTop (𝓝 0)
    := by
  intro i j hL2 F level D localHypothesis6 H b hHmem uH e S hS uₙ hinput
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hinput (fun _ => bot_le)
  intro n
  have hadd := rieszSecondL2MeasurableOperator_add_ae hL2
    (uₙ n - uH) uH
  rw [show (uₙ n - uH) + uH = uₙ n by abel] at hadd
  have hTdiff : rieszSecondL2MeasurableOperator hL2 (uₙ n - uH) =ᵐ[volume]
      rieszSecondL2MeasurableOperator hL2 (uₙ n) -
        rieszSecondL2MeasurableOperator hL2 uH := by
    filter_upwards [hadd] with x hx
    calc
      rieszSecondL2MeasurableOperator hL2 (uₙ n - uH) x =
          (rieszSecondL2MeasurableOperator hL2 (uₙ n - uH) x +
            rieszSecondL2MeasurableOperator hL2 uH x) -
            rieszSecondL2MeasurableOperator hL2 uH x := by ring
      _ = rieszSecondL2MeasurableOperator hL2 (uₙ n) x -
          rieszSecondL2MeasurableOperator hL2 uH x := by
        have hx' : rieszSecondL2MeasurableOperator hL2 (uₙ n) x =
            rieszSecondL2MeasurableOperator hL2 (uₙ n - uH) x +
              rieszSecondL2MeasurableOperator hL2 uH x := by
          simpa only [Pi.add_apply] using hx
        rw [← hx']
  have hdiffmem : MemLp (S n - H) (2 : ℝ≥0∞) volume := (hS n).sub hHmem
  have hdiff : MemLp.toLp (S n - H) hdiffmem = uₙ n - uH := by
    simpa [uₙ, uH] using MemLp.toLp_sub (hS n) hHmem
  calc
    eLpNorm (rieszSecondL2MeasurableOperator hL2 (uₙ n) -
        rieszSecondL2MeasurableOperator hL2 uH)
        (2 : ℝ≥0∞) volume =
        eLpNorm (rieszSecondL2MeasurableOperator hL2 (uₙ n - uH))
          (2 : ℝ≥0∞) volume := eLpNorm_congr_ae hTdiff.symm
    _ ≤ eLpNorm (MemLp.toLp (S n - H) hdiffmem : Vec3 → ℝ)
          (2 : ℝ≥0∞) volume := by
      rw [← hdiff]
      exact rieszSecondL2MeasurableOperator_eLpNorm_le hL2 _
    _ = eLpNorm (uₙ n - uH) (2 : ℝ≥0∞) volume := by rw [hdiff]

theorem rieszSecond_countable_bad_additivity_infinite
    {i j : Fin 3} (hL2 : RieszSecondL2Input i j)
    {F : Vec3 → ℝ} {level : ℝ} (D : CZDecomposition F level)
    [Infinite {Q // Q ∈ D.cubes}]
    (hF : Integrable F volume) (hF₂ : MemLp F (2 : ℝ≥0∞) volume)
    {C_H : ℝ≥0∞} (hC_H : C_H ≠ ∞)
    (hbridge : ∀ Q : {Q // Q ∈ D.cubes},
      (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
        ENNReal.ofReal |(rieszSecondL2MeasurableOperator hL2
          (MemLp.toLp (dyadicBadPart F Q.1)
            (dyadic_bad_part_memLp_two D hF₂ Q)) x)|) ≤
        C_H * ∫⁻ x in dyadicCubeSet Q.1,
          ENNReal.ofReal |dyadicBadPart F Q.1 x|) :
    (∀ᵐ x ∂(volume.restrict
      (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ),
      (rieszSecondL2MeasurableOperator hL2 (MemLp.toLp F hF₂) x -
        rieszSecondL2MeasurableOperator hL2
          (MemLp.toLp (dyadicGoodPart F D.cubes)
            (dyadic_good_part_memLp_two D hF₂)) x) =
        ∑' Q : {Q // Q ∈ D.cubes},
          rieszSecondL2MeasurableOperator hL2
            (MemLp.toLp (dyadicBadPart F Q.1)
              (dyadic_bad_part_memLp_two D hF₂ Q)) x) ∧
    (∀ᵐ x ∂(volume.restrict
      (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ),
      Summable (fun Q : {Q // Q ∈ D.cubes} =>
        |rieszSecondL2MeasurableOperator hL2
          (MemLp.toLp (dyadicBadPart F Q.1)
            (dyadic_bad_part_memLp_two D hF₂ Q)) x|)) := by
  classical
  let U : Set Vec3 := ⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1
  let H : Vec3 → ℝ := fun x => F x - dyadicGoodPart F D.cubes x
  let b : {Q // Q ∈ D.cubes} → Vec3 → ℝ := fun Q =>
    dyadicBadPart F Q.1
  let Tbad : {Q // Q ∈ D.cubes} → Vec3 → ℝ := fun Q =>
    rieszSecondL2MeasurableOperator hL2
      (MemLp.toLp (b Q) (dyadic_bad_part_memLp_two D hF₂ Q))
  have hU : MeasurableSet U := by
    dsimp [U]
    apply MeasurableSet.iUnion
    intro Q
    exact measurableSet_rieszSecondCubeStar_countable Q.1
  have hnormtop : dyadicL1Norm F < ∞ := by
    dsimp [dyadicL1Norm]
    have hne := (lintegral_ofReal_ne_top_iff_integrable
      hF.norm.aestronglyMeasurable
      (ae_of_all _ (fun x => abs_nonneg (F x)))).2 hF.norm
    exact lt_top_iff_ne_top.mpr hne
  have hsumstar := @rieszSecond_countable_bad_additivity_infinite_hsumstar_1 i j hL2 F level D hF₂
    C_H hbridge
  have hsumtop : C_H * (2 * dyadicL1Norm F) < ∞ := by
    exact ENNReal.mul_lt_top (by exact lt_top_iff_ne_top.mpr hC_H)
      (ENNReal.mul_lt_top (by norm_num) hnormtop)
  have hUtop : (∑' Q : {Q // Q ∈ D.cubes},
      ∫⁻ x in Uᶜ, ENNReal.ofReal |Tbad Q x|) < ∞ := by
    calc
      (∑' Q : {Q // Q ∈ D.cubes},
          ∫⁻ x in Uᶜ, ENNReal.ofReal |Tbad Q x|) ≤
          ∑' Q : {Q // Q ∈ D.cubes},
            ∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
              ENNReal.ofReal |Tbad Q x| := by
        apply ENNReal.tsum_le_tsum
        intro Q
        have hsub : Uᶜ ⊆ (rieszSecondCubeStar Q.1)ᶜ := by
          intro x hx hxQ
          exact hx (mem_iUnion.2 ⟨Q, hxQ⟩)
        exact lintegral_mono_set hsub
      _ ≤ C_H * (2 * dyadicL1Norm F) := hsumstar
      _ < ∞ := hsumtop
  have hmeas : ∀ Q : {Q // Q ∈ D.cubes},
      AEMeasurable (fun x => ENNReal.ofReal |Tbad Q x|)
        (volume.restrict Uᶜ) := by
    intro Q
    have hmeas0 : AEMeasurable (fun x => |Tbad Q x|) volume := by
      exact (rieszSecondL2MeasurableOperator_measurable hL2 _).norm.aemeasurable
    exact hmeas0.ennreal_ofReal.mono_measure Measure.restrict_le_self
  have hseries_top : (∫⁻ x in Uᶜ,
      ∑' Q : {Q // Q ∈ D.cubes}, ENNReal.ofReal |Tbad Q x|) < ∞ := by
    rw [lintegral_tsum hmeas]
    exact hUtop
  have habs : ∀ᵐ x ∂(volume.restrict Uᶜ),
      Summable (fun Q : {Q // Q ∈ D.cubes} => |Tbad Q x|) := by
    have htop := ae_lt_top'
      (AEMeasurable.tsum hmeas) hseries_top.ne
    filter_upwards [htop] with x hx
    have htoReal : Summable (fun Q : {Q // Q ∈ D.cubes} =>
        (ENNReal.ofReal |Tbad Q x|).toReal) :=
      ENNReal.summable_toReal hx.ne
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using htoReal
  have hHmem : MemLp H (2 : ℝ≥0∞) volume := by
    simpa only [H] using dyadic_bad_sum_memLp_two D hF₂
  let uH : rieszSecondL2 := MemLp.toLp H hHmem
  let e : ℕ ≃ {Q // Q ∈ D.cubes} :=
    Classical.choice (nonempty_equiv_of_countable (α := ℕ)
      (β := {Q // Q ∈ D.cubes}))
  let S : ℕ → Vec3 → ℝ := fun n x => ∑ k ∈ Finset.range n, b (e k) x
  have hS : ∀ n, MemLp (S n) (2 : ℝ≥0∞) volume := by
    intro n
    simpa only [S, b] using finite_bad_sum_memLp_two_countable D hF₂
      (Finset.range n) e
  let uₙ : ℕ → rieszSecondL2 := fun n => MemLp.toLp (S n) (hS n)
  have hpartial := bad_partial_eLpNorm_tendsto_zero_countable D hF₂
    (e := e)
  have hpartial' : Tendsto (fun n => eLpNorm (S n - H)
      (2 : ℝ≥0∞) volume) atTop (𝓝 0) := by
    simpa only [S, b, H] using hpartial
  have hinput := @rieszSecond_countable_bad_additivity_infinite_hinput_2 F level D (by
    infer_instance) hHmem hS hpartial'
  have hTout := @rieszSecond_countable_bad_additivity_infinite_hTout_3 i j hL2 F level D (by
    infer_instance) hHmem hS hinput
  obtain ⟨ns, hns, htae⟩ :=
    ae_subsequence_of_eLpNorm_tendsto_zero (p := (2 : ℝ≥0∞))
      (by norm_num) hTout
  have hfiniteEq : ∀ n, rieszSecondL2MeasurableOperator hL2
      (uₙ n) =ᵐ[volume]
      (fun x => ∑ k ∈ Finset.range n, Tbad (e k) x) := by
    intro n
    simpa only [S, b, Tbad] using operator_finset_bad_sum_ae_countable
      hL2 D hF₂ (Finset.range n) e
  have hfiniteEqAll : ∀ᵐ x ∂volume, ∀ n,
      rieszSecondL2MeasurableOperator hL2 (uₙ n) x =
        ∑ k ∈ Finset.range n, Tbad (e k) x := by
    rw [ae_all_iff]
    intro n
    exact hfiniteEq n
  have hsum : ∀ᵐ x ∂(volume.restrict Uᶜ),
      Tendsto (fun n => ∑ k ∈ Finset.range n, Tbad (e k) x) atTop
        (𝓝 (∑' Q : {Q // Q ∈ D.cubes}, Tbad Q x)) := by
    filter_upwards [habs] with x hx
    have hnorm : Summable (fun Q : {Q // Q ∈ D.cubes} =>
        ‖Tbad Q x‖) := by
      simpa only [Real.norm_eq_abs] using hx
    have hTsum : HasSum (fun Q : {Q // Q ∈ D.cubes} => Tbad Q x)
        (∑' Q : {Q // Q ∈ D.cubes}, Tbad Q x) := hnorm.of_norm.hasSum
    have hTsumNat : HasSum (fun n : ℕ => Tbad (e n) x)
        (∑' Q : {Q // Q ∈ D.cubes}, Tbad Q x) :=
      (e.hasSum_iff (f := fun Q : {Q // Q ∈ D.cubes} => Tbad Q x)).2 hTsum
    exact hTsumNat.tendsto_sum_nat
  have hleft : rieszSecondL2MeasurableOperator hL2 (MemLp.toLp F hF₂) -
      rieszSecondL2MeasurableOperator hL2
        (MemLp.toLp (dyadicGoodPart F D.cubes)
          (dyadic_good_part_memLp_two D hF₂)) =ᵐ[volume]
      rieszSecondL2MeasurableOperator hL2 uH := by
    have hgoodmem := dyadic_good_part_memLp_two D hF₂
    have htoLp : MemLp.toLp F hF₂ =
        (MemLp.toLp (dyadicGoodPart F D.cubes) hgoodmem : rieszSecondL2) + uH := by
      apply MemLp.toLp_congr hF₂ (hgoodmem.add hHmem)
      filter_upwards [dyadic_good_bad_decomposition_ae D] with x hx
      dsimp [H] at hx ⊢
      linarith only [hx]
    have hadd := rieszSecondL2MeasurableOperator_add_ae hL2
      (MemLp.toLp (dyadicGoodPart F D.cubes) hgoodmem) uH
    have hTF := congrArg (rieszSecondL2MeasurableOperator hL2) htoLp
    filter_upwards [hadd] with x hx
    rw [Pi.sub_apply, hTF, Pi.add_apply] at *
    linarith only [hx]
  have hleftR := ae_restrict_of_ae (s := Uᶜ) hleft
  have htaeR := ae_restrict_of_ae (s := Uᶜ) htae
  have hfiniteAllR := ae_restrict_of_ae (s := Uᶜ) hfiniteEqAll
  refine ⟨?_, ?_⟩
  · filter_upwards [hleftR, htaeR, hsum, hfiniteAllR]
        with x hleftx htaex hsumx hfiniteAll
    have hfiniteEqSub : ∀ᶠ n : ℕ in atTop,
        rieszSecondL2MeasurableOperator hL2 (uₙ (ns n)) x =
          ∑ k ∈ Finset.range (ns n), Tbad (e k) x := by
      exact Filter.Eventually.of_forall (fun n => hfiniteAll (ns n))
    have houtputx : Tendsto (fun n =>
        rieszSecondL2MeasurableOperator hL2 (uₙ (ns n)) x) atTop
        (𝓝 (rieszSecondL2MeasurableOperator hL2 uH x)) :=
      htaex
    have hsumx' : Tendsto (fun n =>
        ∑ k ∈ Finset.range (ns n), Tbad (e k) x) atTop
        (𝓝 (∑' Q : {Q // Q ∈ D.cubes}, Tbad Q x)) :=
      hsumx.comp hns.tendsto_atTop
    have hoperator_sum :
        rieszSecondL2MeasurableOperator hL2 uH x =
          ∑' Q : {Q // Q ∈ D.cubes}, Tbad Q x :=
      tendsto_nhds_unique houtputx
        (hsumx'.congr' (Filter.EventuallyEq.symm hfiniteEqSub))
    calc
      rieszSecondL2MeasurableOperator hL2 (MemLp.toLp F hF₂) x -
          rieszSecondL2MeasurableOperator hL2
            (MemLp.toLp (dyadicGoodPart F D.cubes)
              (dyadic_good_part_memLp_two D hF₂)) x =
          (rieszSecondL2MeasurableOperator hL2 (MemLp.toLp F hF₂) -
            rieszSecondL2MeasurableOperator hL2
              (MemLp.toLp (dyadicGoodPart F D.cubes)
                (dyadic_good_part_memLp_two D hF₂))) x := by rfl
      _ = rieszSecondL2MeasurableOperator hL2 uH x := hleftx
      _ = ∑' Q : {Q // Q ∈ D.cubes}, Tbad Q x := hoperator_sum
  · exact habs

theorem rieszSecond_countable_bad_additivity
    {i j : Fin 3} (hL2 : RieszSecondL2Input i j)
    {F : Vec3 → ℝ} {level : ℝ} (D : CZDecomposition F level)
    (hF : Integrable F volume) (hF₂ : MemLp F (2 : ℝ≥0∞) volume)
    {C_H : ℝ≥0∞} (hC_H : C_H ≠ ∞)
    (hbridge : ∀ Q : {Q // Q ∈ D.cubes},
      (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
        ENNReal.ofReal |(rieszSecondL2MeasurableOperator hL2
          (MemLp.toLp (dyadicBadPart F Q.1)
            (dyadic_bad_part_memLp_two D hF₂ Q)) x)|) ≤
        C_H * ∫⁻ x in dyadicCubeSet Q.1,
          ENNReal.ofReal |dyadicBadPart F Q.1 x|) :
    (∀ᵐ x ∂(volume.restrict
      (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ),
      (rieszSecondL2MeasurableOperator hL2 (MemLp.toLp F hF₂) x -
        rieszSecondL2MeasurableOperator hL2
          (MemLp.toLp (dyadicGoodPart F D.cubes)
            (dyadic_good_part_memLp_two D hF₂)) x) =
        ∑' Q : {Q // Q ∈ D.cubes},
          rieszSecondL2MeasurableOperator hL2
            (MemLp.toLp (dyadicBadPart F Q.1)
              (dyadic_bad_part_memLp_two D hF₂ Q)) x) ∧
    (∀ᵐ x ∂(volume.restrict
      (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ),
      Summable (fun Q : {Q // Q ∈ D.cubes} =>
        |rieszSecondL2MeasurableOperator hL2
          (MemLp.toLp (dyadicBadPart F Q.1)
            (dyadic_bad_part_memLp_two D hF₂ Q)) x|)) := by
  classical
  by_cases hInf : Infinite {Q // Q ∈ D.cubes}
  · have := hInf
    exact rieszSecond_countable_bad_additivity_infinite hL2 D hF hF₂ hC_H hbridge
  · have hFin : Finite {Q // Q ∈ D.cubes} := not_infinite_iff_finite.mp hInf
    have : Finite {Q // Q ∈ D.cubes} := hFin
    have : Fintype {Q // Q ∈ D.cubes} := Fintype.ofFinite _
    let U : Set Vec3 := ⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1
    let b : {Q // Q ∈ D.cubes} → Vec3 → ℝ := fun Q =>
      dyadicBadPart F Q.1
    let Tb : {Q // Q ∈ D.cubes} → Vec3 → ℝ := fun Q =>
      rieszSecondL2MeasurableOperator hL2
        (MemLp.toLp (b Q) (dyadic_bad_part_memLp_two D hF₂ Q))
    have hsumMem : MemLp (fun x => ∑ Q, b Q x)
        (2 : ℝ≥0∞) volume := by
      apply memLp_finsetSum
      intro Q hQ
      exact dyadic_bad_part_memLp_two D hF₂ Q
    let H : Vec3 → ℝ := fun x => F x - dyadicGoodPart F D.cubes x
    have hHmem : MemLp H (2 : ℝ≥0∞) volume := by
      simpa only [H] using dyadic_bad_sum_memLp_two D hF₂
    have hsumEq : (fun x => ∑ Q, b Q x) =ᵐ[volume] H := by
      filter_upwards [dyadic_good_bad_decomposition_ae D] with x hx
      rw [tsum_fintype] at hx
      dsimp [H, b]
      linarith only [hx]
    have hfinite : rieszSecondL2MeasurableOperator hL2
        (MemLp.toLp (fun x => ∑ Q, b Q x) hsumMem) =ᵐ[volume]
        (fun x => ∑ Q, Tb Q x) := by
      simpa only [Tb, b] using operator_finset_bad_sum_ae_countable hL2 D hF₂
        (Finset.univ : Finset {Q // Q ∈ D.cubes}) (fun Q => Q)
    have hFsum : MemLp.toLp F hF₂ =
        (MemLp.toLp (dyadicGoodPart F D.cubes)
          (dyadic_good_part_memLp_two D hF₂) : rieszSecondL2) +
          MemLp.toLp (fun x => ∑ Q, b Q x) hsumMem := by
      apply MemLp.toLp_congr hF₂
      on_goal 1 => exact (dyadic_good_part_memLp_two D hF₂).add hsumMem
      filter_upwards [hsumEq] with x hx
      dsimp [H] at hx
      change F x = dyadicGoodPart F D.cubes x + ∑ Q, b Q x
      linarith only [hx]
    have hadd := rieszSecondL2MeasurableOperator_add_ae hL2
      (MemLp.toLp (dyadicGoodPart F D.cubes)
        (dyadic_good_part_memLp_two D hF₂))
      (MemLp.toLp (fun x => ∑ Q, b Q x) hsumMem)
    have hleft : rieszSecondL2MeasurableOperator hL2 (MemLp.toLp F hF₂) -
        rieszSecondL2MeasurableOperator hL2
          (MemLp.toLp (dyadicGoodPart F D.cubes)
            (dyadic_good_part_memLp_two D hF₂)) =ᵐ[volume]
        rieszSecondL2MeasurableOperator hL2
          (MemLp.toLp (fun x => ∑ Q, b Q x) hsumMem) := by
      have hTF := congrArg (rieszSecondL2MeasurableOperator hL2) hFsum
      filter_upwards [hadd] with x hx
      rw [Pi.sub_apply, hTF, Pi.add_apply] at *
      linarith only [hx]
    have hleftR := ae_restrict_of_ae (s := Uᶜ) hleft
    have hfiniteR := ae_restrict_of_ae (s := Uᶜ) hfinite
    refine ⟨?_, ?_⟩
    · filter_upwards [hleftR, hfiniteR] with x hx hfx
      calc
        rieszSecondL2MeasurableOperator hL2 (MemLp.toLp F hF₂) x -
            rieszSecondL2MeasurableOperator hL2
              (MemLp.toLp (dyadicGoodPart F D.cubes)
                (dyadic_good_part_memLp_two D hF₂)) x =
            rieszSecondL2MeasurableOperator hL2
              (MemLp.toLp (fun x => ∑ Q, b Q x) hsumMem) x := hx
        _ = ∑' Q, Tb Q x := by
          rw [tsum_fintype]
          exact hfx
    · filter_upwards [] with x
      apply summable_of_hasFiniteSupport
      exact Set.Finite.subset Set.finite_univ (Set.subset_univ _)

end CKN.Foundation.Euclidean
