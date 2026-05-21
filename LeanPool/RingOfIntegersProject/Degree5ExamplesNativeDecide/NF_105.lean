/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.CertificateDedekind
import LeanPool.RingOfIntegersProject.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import LeanPool.RingOfIntegersProject.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible105

-- Number field with label 5.3.2025000000.6 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 35*X^3 - 70*X^2 + 210*X + 1916 
lemma T_def : T = X^5 - 35*X^3 - 70*X^2 + 210*X + 1916 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [1916, 210, -70, -35, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, a^3, 1/446*a^4 + 55/223*a^3 + 23/446*a^2 - 108/223*a + 44/223] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  446
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![446, 0, 0, 0, 0], ![0, 446, 0, 0, 0], ![0, 0, 446, 0, 0], ![0, 0, 0, 446, 0], ![88, -216, 23, 110, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-88, 216, -23, -110, 446],![-26, 53, -6, -27, 110]], 
![![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-88, 216, -23, -110, 446],![-1916, -210, 70, 35, 0],![-484, -28, 14, -6, 58]], 
![![0, 0, 0, 1, 0],![-88, 216, -23, -110, 446],![-1916, -210, 70, 35, 0],![-3080, 5644, -1015, -3780, 15610],![-980, 1294, -238, -892, 3704]], 
![![0, 0, 0, 0, 1],![-26, 53, -6, -27, 110],![-484, -28, 14, -6, 58],![-980, 1294, -238, -892, 3704],![-294, 298, -56, -212, 885]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-446]],![[], [], [], [-198916], [-49060, -446]],![[], [], [-198916], [0, -198916], [-25868, -49060, -446]],![[], [-446], [-49060, -446], [-25868, -49060, -446], [-12398, -12181, -220, -1]]]
 h := Adj
 honed := by native_decide
 hd := by norm_num
 hcc := by native_decide 
 hin := by native_decide
 hsymma := by native_decide
 hc_le := by native_decide 

lemma T_degree : T.natDegree = 5 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B : Basis (Fin 5) ℤ O := basisOfBuilderLists T l BQ
noncomputable def B' : Basis (Fin 5) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 5) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ 
def Table : Fin 5 → Fin 5 → List ℤ := 
 ![ ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-88, 216, -23, -110, 446], [-26, 53, -6, -27, 110]], 
 ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-88, 216, -23, -110, 446], [-1916, -210, 70, 35, 0], [-484, -28, 14, -6, 58]], 
 ![[0, 0, 0, 1, 0], [-88, 216, -23, -110, 446], [-1916, -210, 70, 35, 0], [-3080, 5644, -1015, -3780, 15610], [-980, 1294, -238, -892, 3704]], 
 ![[0, 0, 0, 0, 1], [-26, 53, -6, -27, 110], [-484, -28, 14, -6, 58], [-980, 1294, -238, -892, 3704], [-294, 298, -56, -212, 885]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp223: Fact $ Nat.Prime 223 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  3
 a' := [2]
 b' :=  [0, 1, 1]
 k := [1, 0, 2, 0, 1]
 f := [-638, -69, 25, 13, 1]
 g :=  [2, 1, 2, 1]
 h :=  [1, 1, 1]
 a :=  [2, 2]
 b :=  [1, 0, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [-383, -41, 15, 8, 1]
 g :=  [1, 1]
 h :=  [1, 4, 1, 4, 1]
 a :=  [1]
 b :=  [4, 2, 3, 4]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 223] where
 n := 4
 p := ![2, 3, 5, 223]
 exp := ![8, 4, 8, 2]
 pdgood := [3, 5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp223.out
 a := [612090000000, -209002500000, -230265000000, -45517500000]
 b := [-3666474000000, -1149507000000, -85648500000, 46053000000, 9103500000]
 hab := by native_decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 2
 n := 3
 t :=  3
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 1, 0]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 0, 1]]
 v_ind := ![1, 2]
 w_ind := ![0, 2, 4]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 1, 1, 1, 0],![0, 1, 0, 0, 0],![1, 1, 0, 0, 1],![0, 0, 1, 1, 0],![0, 1, 0, 1, 0]]
 w1 := ![1, 1]
 w2 := ![0, 1, 0]
 a := ![![-6155, -1954],![-176, -43],![-1566, -522],![-5980, -1912],![-6002, -2072]]
 c := ![![-6218, 9056, 16948],![-88, 304, 446],![-1349, 2360, 4344],![-6130, 8751, 16502],![-4258, 9080, 16725]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 

noncomputable def M223 : MaximalOrderCertificateOfUnramifiedLists 223 O Om hm where
 n := 5
 t :=  1
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [135, 216, 200, 113, 0], [197, 53, 217, 196, 110]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [135, 216, 200, 113, 0], [91, 13, 70, 35, 0], [185, 195, 14, 217, 58]], 
![[0, 0, 0, 1, 0], [135, 216, 200, 113, 0], [91, 13, 70, 35, 0], [42, 69, 100, 11, 0], [135, 179, 208, 0, 136]], 
![[0, 0, 0, 0, 1], [197, 53, 217, 196, 110], [185, 195, 14, 217, 58], [135, 179, 208, 0, 136], [152, 75, 167, 11, 216]]]
 hTMod := by native_decide
 hle := by native_decide
 w := ![![1, 0, 0, 0, 0],![37, 176, 109, 138, 0],![192, 215, 205, 23, 0],![116, 181, 179, 66, 0],![218, 121, 148, 126, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by native_decide
 hwFrobComp := by native_decide 

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 223]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 223 O Om hm M223
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 223] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
