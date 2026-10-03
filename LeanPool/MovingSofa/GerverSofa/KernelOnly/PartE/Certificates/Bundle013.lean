/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch018`.
* `GerverSofa.KernelOnly.PartE.Certificates.Batch044`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCellsfa7ef730fc

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022003000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `000022003001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `000022003002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `000022003003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `000022003010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `000022003011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `000022003012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `000022003013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `000022003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `000022003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `000022003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `000022003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `000022003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `000022003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `000022003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `000022003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00002200)))

/-- Subcell `0000220030002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022003000)))

/-- Subcell `0000220030003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022003000)))

/-- Subcell `0000220030012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022003001)))

/-- Subcell `0000220030013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022003001)))

/-- Subcell `0000220030102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022003010)))

/-- Subcell `0000220030103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022003010)))

/-- Subcell `0000220030112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022003011)))

/-- Subcell `0000220030113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022003011)))

/-- Subcell `0000220030113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220030113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022003011)))

end GerverSofa.PartE.CertificateCellsfa7ef730fc

namespace GerverSofa.PartE.CoverCertificate1bb21a49a4

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLL
    (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate1bb21a49a4

namespace GerverSofa.PartE.CoverCertificatec9db3a1aba

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLL
    (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificatec9db3a1aba

namespace GerverSofa.PartE.CoverCertificatefb03004e1f

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childHL (childLH (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificatefb03004e1f

namespace GerverSofa.PartE.CoverCertificate045cecfd86

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childHL (childLH (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate045cecfd86

namespace GerverSofa.PartE.CoverCertificatef837300024

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childHL (childLH (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell020 : AngleCell :=
  childLL cell02

private abbrev cell021 : AngleCell :=
  childLH cell02

private abbrev cell022 : AngleCell :=
  childHL cell02

private abbrev cell023 : AngleCell :=
  childHH cell02

private abbrev cell030 : AngleCell :=
  childLL cell03

private abbrev cell031 : AngleCell :=
  childLH cell03

private abbrev cell032 : AngleCell :=
  childHL cell03

private abbrev cell033 : AngleCell :=
  childHH cell03

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

private abbrev cell120 : AngleCell :=
  childLL cell12

private abbrev cell121 : AngleCell :=
  childLH cell12

private abbrev cell122 : AngleCell :=
  childHL cell12

private abbrev cell123 : AngleCell :=
  childHH cell12

private abbrev cell130 : AngleCell :=
  childLL cell13

private abbrev cell131 : AngleCell :=
  childLH cell13

private abbrev cell132 : AngleCell :=
  childHL cell13

private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificatef837300024

namespace GerverSofa.PartE.CoverCertificate2943ba0b5c

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childHL (childLH (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell020 : AngleCell :=
  childLL cell02

private abbrev cell021 : AngleCell :=
  childLH cell02

private abbrev cell022 : AngleCell :=
  childHL cell02

private abbrev cell023 : AngleCell :=
  childHH cell02

private abbrev cell030 : AngleCell :=
  childLL cell03

private abbrev cell031 : AngleCell :=
  childLH cell03

private abbrev cell032 : AngleCell :=
  childHL cell03

private abbrev cell033 : AngleCell :=
  childHH cell03

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

private abbrev cell120 : AngleCell :=
  childLL cell12

private abbrev cell121 : AngleCell :=
  childLH cell12

private abbrev cell122 : AngleCell :=
  childHL cell12

private abbrev cell123 : AngleCell :=
  childHH cell12

private abbrev cell130 : AngleCell :=
  childLL cell13

private abbrev cell131 : AngleCell :=
  childLH cell13

private abbrev cell132 : AngleCell :=
  childHL cell13

private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificate2943ba0b5c

namespace GerverSofa.PartE.CoverCertificate42a60e756f

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childHL (childLH (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate42a60e756f

namespace GerverSofa.PartE.CoverCertificate0cee658f4b

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childHL (childLH (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate0cee658f4b

namespace GerverSofa.PartE.CoverCertificateeb376f6b8e

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childHL (childLH (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell020 : AngleCell :=
  childLL cell02

private abbrev cell021 : AngleCell :=
  childLH cell02

private abbrev cell022 : AngleCell :=
  childHL cell02

private abbrev cell023 : AngleCell :=
  childHH cell02

private abbrev cell030 : AngleCell :=
  childLL cell03

private abbrev cell031 : AngleCell :=
  childLH cell03

private abbrev cell032 : AngleCell :=
  childHL cell03

private abbrev cell033 : AngleCell :=
  childHH cell03

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

private abbrev cell120 : AngleCell :=
  childLL cell12

private abbrev cell121 : AngleCell :=
  childLH cell12

private abbrev cell122 : AngleCell :=
  childHL cell12

private abbrev cell123 : AngleCell :=
  childHH cell12

private abbrev cell130 : AngleCell :=
  childLL cell13

private abbrev cell131 : AngleCell :=
  childLH cell13

private abbrev cell132 : AngleCell :=
  childHL cell13

private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificateeb376f6b8e

namespace GerverSofa.PartE.CoverCertificate1e208f1b6e

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childHL (childLH (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell020 : AngleCell :=
  childLL cell02

private abbrev cell021 : AngleCell :=
  childLH cell02

private abbrev cell022 : AngleCell :=
  childHL cell02

private abbrev cell023 : AngleCell :=
  childHH cell02

private abbrev cell030 : AngleCell :=
  childLL cell03

private abbrev cell031 : AngleCell :=
  childLH cell03

private abbrev cell032 : AngleCell :=
  childHL cell03

private abbrev cell033 : AngleCell :=
  childHH cell03

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

private abbrev cell120 : AngleCell :=
  childLL cell12

private abbrev cell121 : AngleCell :=
  childLH cell12

private abbrev cell122 : AngleCell :=
  childHL cell12

private abbrev cell123 : AngleCell :=
  childHH cell12

private abbrev cell130 : AngleCell :=
  childLL cell13

private abbrev cell131 : AngleCell :=
  childLH cell13

private abbrev cell132 : AngleCell :=
  childHL cell13

private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificate1e208f1b6e

namespace GerverSofa.PartE.CoverCertificate6fd62aabed

private abbrev cellRoot : AngleCell :=
  (childHL (childHL (childLH (childLH (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate6fd62aabed

namespace GerverSofa.PartE.CoverCertificate22515ac7bd

private abbrev cellRoot : AngleCell :=
  (childHH (childHL (childLH (childLH (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate22515ac7bd

namespace GerverSofa.PartE.CoverCertificatebad9a9b575

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childHH (childLH (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificatebad9a9b575

namespace GerverSofa.PartE.CoverCertificate13a680926b

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childHH (childLH (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate13a680926b

namespace GerverSofa.PartE.CoverCertificatebdefa88d14

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childHH (childLH (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell020 : AngleCell :=
  childLL cell02

private abbrev cell021 : AngleCell :=
  childLH cell02

private abbrev cell022 : AngleCell :=
  childHL cell02

private abbrev cell023 : AngleCell :=
  childHH cell02

private abbrev cell030 : AngleCell :=
  childLL cell03

private abbrev cell031 : AngleCell :=
  childLH cell03

private abbrev cell032 : AngleCell :=
  childHL cell03

private abbrev cell033 : AngleCell :=
  childHH cell03

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

private abbrev cell120 : AngleCell :=
  childLL cell12

private abbrev cell121 : AngleCell :=
  childLH cell12

private abbrev cell122 : AngleCell :=
  childHL cell12

private abbrev cell123 : AngleCell :=
  childHH cell12

private abbrev cell130 : AngleCell :=
  childLL cell13

private abbrev cell131 : AngleCell :=
  childLH cell13

private abbrev cell132 : AngleCell :=
  childHL cell13

private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificatebdefa88d14

namespace GerverSofa.PartE.CoverCertificateb54a5d06ec

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childHH (childLH (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell020 : AngleCell :=
  childLL cell02

private abbrev cell021 : AngleCell :=
  childLH cell02

private abbrev cell022 : AngleCell :=
  childHL cell02

private abbrev cell023 : AngleCell :=
  childHH cell02

private abbrev cell030 : AngleCell :=
  childLL cell03

private abbrev cell031 : AngleCell :=
  childLH cell03

private abbrev cell032 : AngleCell :=
  childHL cell03

private abbrev cell033 : AngleCell :=
  childHH cell03

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

private abbrev cell120 : AngleCell :=
  childLL cell12

private abbrev cell121 : AngleCell :=
  childLH cell12

private abbrev cell122 : AngleCell :=
  childHL cell12

private abbrev cell123 : AngleCell :=
  childHH cell12

private abbrev cell130 : AngleCell :=
  childLL cell13

private abbrev cell131 : AngleCell :=
  childLH cell13

private abbrev cell132 : AngleCell :=
  childHL cell13

private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificateb54a5d06ec

namespace GerverSofa.PartE.CertificateCells5e16eb2f1b

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells5e16eb2f1b

namespace GerverSofa.PartE.CertificateCellsb7fa51f50b

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsb7fa51f50b

namespace GerverSofa.PartE.CertificateCellsd618452127

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsd618452127

namespace GerverSofa.PartE.CertificateCells82d3525350

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells82d3525350

namespace GerverSofa.PartE.CertificateCells632f810978

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells632f810978

namespace GerverSofa.PartE.CertificateCells15b8174174

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells15b8174174

namespace GerverSofa.PartE.CertificateCells1f25007fe8

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells1f25007fe8

namespace GerverSofa.PartE.CertificateCells1e9acaa8be

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells1e9acaa8be

namespace GerverSofa.PartE.CertificateCells231d66ab0c

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells231d66ab0c

namespace GerverSofa.PartE.CertificateCells2c11250698

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells2c11250698

namespace GerverSofa.PartE.CertificateCells3ce31f23ce

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells3ce31f23ce

namespace GerverSofa.PartE.CertificateCells3c3d48c1eb

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells3c3d48c1eb

namespace GerverSofa.PartE.CertificateCells4d022b961f

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells4d022b961f

namespace GerverSofa.PartE.CertificateCells9798c9c840

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells9798c9c840

namespace GerverSofa.PartE.CertificateCells6832cee036

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells6832cee036

namespace GerverSofa.PartE.CertificateCellsab896aa443

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsab896aa443

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6ProofBatch0bae0a82ed09fca0`.
-/

public section

noncomputable section

section

/-! E24KC6 explicit proof-producing certificate batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsfa7ef730fc

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsfa7ef730fc

open CertificateCellsfa7ef730fc
theorem e24KC2ThetaAboveLeaf0000220022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00002200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00002200))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00002200))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00002200))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00002200))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00002200))) h)
theorem e24KC2ThetaAboveLeaf0000220023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00002200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00002200))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00002200))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00002200))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00002200))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00002200))) h)
theorem cover_subtree_98370144a0ae :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022003000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003000)
    (by
      have h : ((childLL (childLL thetaAboveCell000022003000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL thetaAboveCell000022003000)) h)
    (by
      have h : ((childLH (childLL thetaAboveCell000022003000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL thetaAboveCell000022003000)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022003000))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022003000))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022003000))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022003000))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022003000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022003000))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022003000))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022003000))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022003000))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022003000))) h))

theorem cover_subtree_2b8c79c37576 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022003000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003000)
    (by
      have h : ((childLL (childLH thetaAboveCell000022003000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH thetaAboveCell000022003000)) h)
    (by
      have h : ((childLH (childLH thetaAboveCell000022003000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH thetaAboveCell000022003000)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022003000))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022003000))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022003000))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022003000))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022003000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022003000))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022003000))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022003000))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022003000))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022003000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022003000))) h))

theorem cover_subtree_c9f10be4f818 :
    adaptiveCoverCheck 4 (childLL (childLL (childHL thetaAboveCell000022003000))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL
    thetaAboveCell000022003000)))
    (by
      have h : (thetaAboveCell0000220030002000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002000 h)
    (by
      have h : (thetaAboveCell0000220030002001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002002
        (by
          have h : ((childLL thetaAboveCell0000220030002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002002) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002002) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002002) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002003
        (by
          have h : ((childLL thetaAboveCell0000220030002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002003) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002003) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002003) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002003) h))

theorem cover_subtree_b44dc0179b82 :
    adaptiveCoverCheck 4 (childLH (childLL (childHL thetaAboveCell000022003000))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL
    thetaAboveCell000022003000)))
    (by
      have h : (thetaAboveCell0000220030002010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002010 h)
    (by
      have h : (thetaAboveCell0000220030002011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002012
        (by
          have h : ((childLL thetaAboveCell0000220030002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002012) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002012) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002012) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002013
        (by
          have h : ((childLL thetaAboveCell0000220030002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002013) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002013) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002013) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002013) h))

theorem cover_subtree_2d51606740be :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022003000))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
    thetaAboveCell000022003000)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002020
        (by
          have h : ((childLL thetaAboveCell0000220030002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002020) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002020) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002020) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002021
        (by
          have h : ((childLL thetaAboveCell0000220030002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002021) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002021) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002021) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002022
        (by
          have h : ((childLL thetaAboveCell0000220030002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002022) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002022) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002022) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002023
        (by
          have h : ((childLL thetaAboveCell0000220030002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002023) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002023) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002023) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002023) h))

theorem cover_subtree_84975093d7db :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022003000))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
    thetaAboveCell000022003000)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002030
        (by
          have h : ((childLL thetaAboveCell0000220030002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002030) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002030) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002030) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002031
        (by
          have h : ((childLL thetaAboveCell0000220030002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002031) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002031) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002031) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002032
        (by
          have h : ((childLL thetaAboveCell0000220030002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002032) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002032) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002032) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002033
        (by
          have h : ((childLL thetaAboveCell0000220030002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002033) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002033) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002033) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002033) h))

theorem cover_subtree_ba9d19bd9151 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022003000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022003000))
    cover_subtree_c9f10be4f818
    cover_subtree_b44dc0179b82
    cover_subtree_2d51606740be
    cover_subtree_84975093d7db

theorem cover_subtree_625b3384c249 :
    adaptiveCoverCheck 4 (childLL (childLH (childHL thetaAboveCell000022003000))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL
    thetaAboveCell000022003000)))
    (by
      have h : (thetaAboveCell0000220030002100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002100 h)
    (by
      have h : (thetaAboveCell0000220030002101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002102
        (by
          have h : ((childLL thetaAboveCell0000220030002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002102) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002102) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002102) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002103
        (by
          have h : ((childLL thetaAboveCell0000220030002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002103) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002103) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002103) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002103) h))

theorem cover_subtree_90e4b8e577d3 :
    adaptiveCoverCheck 4 (childLH (childLH (childHL thetaAboveCell000022003000))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHL
    thetaAboveCell000022003000)))
    (by
      have h : (thetaAboveCell0000220030002110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002110 h)
    (by
      have h : (thetaAboveCell0000220030002111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002112
        (by
          have h : ((childLL thetaAboveCell0000220030002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002112) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002112) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002112) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002113
        (by
          have h : ((childLL thetaAboveCell0000220030002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002113) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002113) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002113) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002113) h))

theorem cover_subtree_675556e82299 :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022003000))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
    thetaAboveCell000022003000)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002120
        (by
          have h : ((childLL thetaAboveCell0000220030002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002120) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002120) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002120) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002121
        (by
          have h : ((childLL thetaAboveCell0000220030002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002121) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002121) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002121) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002122
        (by
          have h : ((childLL thetaAboveCell0000220030002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002122) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002122) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002122) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002123
        (by
          have h : ((childLL thetaAboveCell0000220030002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002123) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002123) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002123) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002123) h))

theorem cover_subtree_a828876ee758 :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022003000))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
    thetaAboveCell000022003000)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002130
        (by
          have h : ((childLL thetaAboveCell0000220030002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002130) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002130) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002130) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002131
        (by
          have h : ((childLL thetaAboveCell0000220030002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002131) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002131) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002131) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002132
        (by
          have h : ((childLL thetaAboveCell0000220030002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002132) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002132) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002132) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030002133
        (by
          have h : ((childLL thetaAboveCell0000220030002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030002133) h)
        (by
          have h : ((childLH thetaAboveCell0000220030002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030002133) h)
        (by
          have h : ((childHL thetaAboveCell0000220030002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030002133) h)
        (by
          have h : ((childHH thetaAboveCell0000220030002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030002133) h))

theorem cover_subtree_ab8ac75e68d0 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022003000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022003000))
    cover_subtree_625b3384c249
    cover_subtree_90e4b8e577d3
    cover_subtree_675556e82299
    cover_subtree_a828876ee758

theorem cover_subtree_bdc92ad9349d :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022003000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022003000))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022003000)))
        (by
          have h : (thetaAboveCell0000220030002200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002200 h)
        (by
          have h : (thetaAboveCell0000220030002201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002201 h)
        (by
          have h : (thetaAboveCell0000220030002202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002202 h)
        (by
          have h : (thetaAboveCell0000220030002203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022003000)))
        (by
          have h : (thetaAboveCell0000220030002210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002210 h)
        (by
          have h : (thetaAboveCell0000220030002211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002211 h)
        (by
          have h : (thetaAboveCell0000220030002212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002212 h)
        (by
          have h : (thetaAboveCell0000220030002213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022003000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022003000))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022003000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022003000))) h)

theorem cover_subtree_d20715622b71 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022003000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022003000))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022003000)))
        (by
          have h : (thetaAboveCell0000220030002300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002300 h)
        (by
          have h : (thetaAboveCell0000220030002301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002301 h)
        (by
          have h : (thetaAboveCell0000220030002302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002302 h)
        (by
          have h : (thetaAboveCell0000220030002303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022003000)))
        (by
          have h : (thetaAboveCell0000220030002310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002310 h)
        (by
          have h : (thetaAboveCell0000220030002311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002311 h)
        (by
          have h : (thetaAboveCell0000220030002312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002312 h)
        (by
          have h : (thetaAboveCell0000220030002313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030002313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022003000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022003000))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022003000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022003000))) h)

theorem cover_subtree_b30ba9777925 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022003000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022003000)
    cover_subtree_ba9d19bd9151
    cover_subtree_ab8ac75e68d0
    cover_subtree_bdc92ad9349d
    cover_subtree_d20715622b71

theorem cover_subtree_ee2f6d25ebfc :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022003000))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
    thetaAboveCell000022003000)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003020
        (by
          have h : ((childLL thetaAboveCell0000220030003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003020) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003020) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003020) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003021
        (by
          have h : ((childLL thetaAboveCell0000220030003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003021) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003021) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003021) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003022
        (by
          have h : ((childLL thetaAboveCell0000220030003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003022) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003022) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003022) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003023
        (by
          have h : ((childLL thetaAboveCell0000220030003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003023) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003023) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003023) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003023) h))

theorem cover_subtree_a96993ac001b :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022003000))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
    thetaAboveCell000022003000)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003030
        (by
          have h : ((childLL thetaAboveCell0000220030003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003030) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003030) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003030) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003031
        (by
          have h : ((childLL thetaAboveCell0000220030003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003031) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003031) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003031) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003032
        (by
          have h : ((childLL thetaAboveCell0000220030003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003032) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003032) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003032) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003033
        (by
          have h : ((childLL thetaAboveCell0000220030003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003033) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003033) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003033) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003033) h))

theorem cover_subtree_7c880bebec81 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022003000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022003000))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHH
        thetaAboveCell000022003000)))
        (by
          have h : (thetaAboveCell0000220030003000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003000 h)
        (by
          have h : (thetaAboveCell0000220030003001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003001 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003002
            (by
              have h : ((childLL thetaAboveCell0000220030003002)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003002)
                h)
            (by
              have h : ((childLH thetaAboveCell0000220030003002)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003002)
                h)
            (by
              have h : ((childHL thetaAboveCell0000220030003002)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003002)
                h)
            (by
              have h : ((childHH thetaAboveCell0000220030003002)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003002)
                h))
        (by
          have h : (thetaAboveCell0000220030003003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHH
        thetaAboveCell000022003000)))
        (by
          have h : (thetaAboveCell0000220030003010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003010 h)
        (by
          have h : (thetaAboveCell0000220030003011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003011 h)
        (by
          have h : (thetaAboveCell0000220030003012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003012 h)
        (by
          have h : (thetaAboveCell0000220030003013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003013 h))
    cover_subtree_ee2f6d25ebfc
    cover_subtree_a96993ac001b

theorem cover_subtree_cde3dc3c4679 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022003000))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
    thetaAboveCell000022003000)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003120
        (by
          have h : ((childLL thetaAboveCell0000220030003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003120) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003120) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003120) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003121
        (by
          have h : ((childLL thetaAboveCell0000220030003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003121) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003121) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003121) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003122
        (by
          have h : ((childLL thetaAboveCell0000220030003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003122) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003122) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003122) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003123
        (by
          have h : ((childLL thetaAboveCell0000220030003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003123) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003123) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003123) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003123) h))

theorem cover_subtree_026c8979d7e8 :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022003000))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
    thetaAboveCell000022003000)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003130
        (by
          have h : ((childLL thetaAboveCell0000220030003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003130) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003130) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003130) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003131
        (by
          have h : ((childLL thetaAboveCell0000220030003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003131) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003131) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003131) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003132
        (by
          have h : ((childLL thetaAboveCell0000220030003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003132) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003132) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003132) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030003133
        (by
          have h : ((childLL thetaAboveCell0000220030003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030003133) h)
        (by
          have h : ((childLH thetaAboveCell0000220030003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030003133) h)
        (by
          have h : ((childHL thetaAboveCell0000220030003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030003133) h)
        (by
          have h : ((childHH thetaAboveCell0000220030003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030003133) h))

theorem cover_subtree_e9a5f301f08e :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022003000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022003000))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHH
        thetaAboveCell000022003000)))
        (by
          have h : (thetaAboveCell0000220030003100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003100 h)
        (by
          have h : (thetaAboveCell0000220030003101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003101 h)
        (by
          have h : (thetaAboveCell0000220030003102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003102 h)
        (by
          have h : (thetaAboveCell0000220030003103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHH
        thetaAboveCell000022003000)))
        (by
          have h : (thetaAboveCell0000220030003110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003110 h)
        (by
          have h : (thetaAboveCell0000220030003111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003111 h)
        (by
          have h : (thetaAboveCell0000220030003112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003112 h)
        (by
          have h : (thetaAboveCell0000220030003113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003113 h))
    cover_subtree_cde3dc3c4679
    cover_subtree_026c8979d7e8

theorem cover_subtree_6c8da8a57403 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022003000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022003000))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022003000)))
        (by
          have h : (thetaAboveCell0000220030003200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003200 h)
        (by
          have h : (thetaAboveCell0000220030003201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003201 h)
        (by
          have h : (thetaAboveCell0000220030003202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003202 h)
        (by
          have h : (thetaAboveCell0000220030003203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022003000)))
        (by
          have h : (thetaAboveCell0000220030003210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003210 h)
        (by
          have h : (thetaAboveCell0000220030003211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003211 h)
        (by
          have h : (thetaAboveCell0000220030003212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003212 h)
        (by
          have h : (thetaAboveCell0000220030003213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022003000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022003000))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022003000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022003000))) h)

theorem cover_subtree_c7667f731e87 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022003000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022003000))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022003000)))
        (by
          have h : (thetaAboveCell0000220030003300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003300 h)
        (by
          have h : (thetaAboveCell0000220030003301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003301 h)
        (by
          have h : (thetaAboveCell0000220030003302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003302 h)
        (by
          have h : (thetaAboveCell0000220030003303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022003000)))
        (by
          have h : (thetaAboveCell0000220030003310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003310 h)
        (by
          have h : (thetaAboveCell0000220030003311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003311 h)
        (by
          have h : (thetaAboveCell0000220030003312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003312 h)
        (by
          have h : (thetaAboveCell0000220030003313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030003313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022003000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022003000))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022003000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022003000))) h)

theorem cover_subtree_d916df227547 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022003000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022003000)
    cover_subtree_7c880bebec81
    cover_subtree_e9a5f301f08e
    cover_subtree_6c8da8a57403
    cover_subtree_c7667f731e87

theorem cover_subtree_df29b2bfe6c5 :
    adaptiveCoverCheck 7 thetaAboveCell000022003000 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003000
    cover_subtree_98370144a0ae
    cover_subtree_2b8c79c37576
    cover_subtree_b30ba9777925
    cover_subtree_d916df227547

theorem cover_subtree_b0fbdd86b439 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022003001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003001)
    (by
      have h : ((childLL (childLL thetaAboveCell000022003001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL thetaAboveCell000022003001)) h)
    (by
      have h : ((childLH (childLL thetaAboveCell000022003001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL thetaAboveCell000022003001)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022003001))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022003001))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022003001))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022003001))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022003001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022003001))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022003001))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022003001))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022003001))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022003001))) h))

theorem cover_subtree_f6d73cfc8f96 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022003001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003001)
    (by
      have h : ((childLL (childLH thetaAboveCell000022003001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH thetaAboveCell000022003001)) h)
    (by
      have h : ((childLH (childLH thetaAboveCell000022003001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH thetaAboveCell000022003001)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022003001))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022003001))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022003001))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022003001))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022003001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022003001))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022003001))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022003001))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022003001))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022003001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022003001))) h))

theorem cover_subtree_b01bf826b90b :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022003001))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
    thetaAboveCell000022003001)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012020
        (by
          have h : ((childLL thetaAboveCell0000220030012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012020) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012020) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012020) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012021
        (by
          have h : ((childLL thetaAboveCell0000220030012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012021) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012021) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012021) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012022
        (by
          have h : ((childLL thetaAboveCell0000220030012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012022) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012022) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012022) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012023
        (by
          have h : ((childLL thetaAboveCell0000220030012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012023) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012023) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012023) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012023) h))

theorem cover_subtree_97058acb92ef :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022003001))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
    thetaAboveCell000022003001)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012030
        (by
          have h : ((childLL thetaAboveCell0000220030012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012030) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012030) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012030) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012031
        (by
          have h : ((childLL thetaAboveCell0000220030012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012031) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012031) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012031) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012032
        (by
          have h : ((childLL thetaAboveCell0000220030012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012032) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012032) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012032) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012033
        (by
          have h : ((childLL thetaAboveCell0000220030012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012033) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012033) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012033) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012033) h))

theorem cover_subtree_6f0d223fa251 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022003001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022003001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030012000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012000 h)
        (by
          have h : (thetaAboveCell0000220030012001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012001 h)
        (by
          have h : (thetaAboveCell0000220030012002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012002 h)
        (by
          have h : (thetaAboveCell0000220030012003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030012010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012010 h)
        (by
          have h : (thetaAboveCell0000220030012011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012011 h)
        (by
          have h : (thetaAboveCell0000220030012012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012012 h)
        (by
          have h : (thetaAboveCell0000220030012013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012013 h))
    cover_subtree_b01bf826b90b
    cover_subtree_97058acb92ef

theorem cover_subtree_587871b3f6fc :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022003001))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
    thetaAboveCell000022003001)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012120
        (by
          have h : ((childLL thetaAboveCell0000220030012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012120) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012120) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012120) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012121
        (by
          have h : ((childLL thetaAboveCell0000220030012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012121) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012121) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012121) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012122
        (by
          have h : ((childLL thetaAboveCell0000220030012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012122) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012122) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012122) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012123
        (by
          have h : ((childLL thetaAboveCell0000220030012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012123) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012123) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012123) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012123) h))

theorem cover_subtree_665ba5a76616 :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022003001))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
    thetaAboveCell000022003001)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012130
        (by
          have h : ((childLL thetaAboveCell0000220030012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012130) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012130) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012130) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012131
        (by
          have h : ((childLL thetaAboveCell0000220030012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012131) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012131) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012131) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012132
        (by
          have h : ((childLL thetaAboveCell0000220030012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012132) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012132) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012132) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030012133
        (by
          have h : ((childLL thetaAboveCell0000220030012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030012133) h)
        (by
          have h : ((childLH thetaAboveCell0000220030012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030012133) h)
        (by
          have h : ((childHL thetaAboveCell0000220030012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030012133) h)
        (by
          have h : ((childHH thetaAboveCell0000220030012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030012133) h))

theorem cover_subtree_17de4b0fb6aa :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022003001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022003001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030012100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012100 h)
        (by
          have h : (thetaAboveCell0000220030012101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012101 h)
        (by
          have h : (thetaAboveCell0000220030012102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012102 h)
        (by
          have h : (thetaAboveCell0000220030012103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHL
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030012110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012110 h)
        (by
          have h : (thetaAboveCell0000220030012111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012111 h)
        (by
          have h : (thetaAboveCell0000220030012112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012112 h)
        (by
          have h : (thetaAboveCell0000220030012113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012113 h))
    cover_subtree_587871b3f6fc
    cover_subtree_665ba5a76616

theorem cover_subtree_2dc0f946809c :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022003001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022003001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030012200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012200 h)
        (by
          have h : (thetaAboveCell0000220030012201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012201 h)
        (by
          have h : (thetaAboveCell0000220030012202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012202 h)
        (by
          have h : (thetaAboveCell0000220030012203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030012210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012210 h)
        (by
          have h : (thetaAboveCell0000220030012211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012211 h)
        (by
          have h : (thetaAboveCell0000220030012212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012212 h)
        (by
          have h : (thetaAboveCell0000220030012213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022003001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022003001))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022003001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022003001))) h)

theorem cover_subtree_9ae7d1f286db :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022003001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022003001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030012300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012300 h)
        (by
          have h : (thetaAboveCell0000220030012301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012301 h)
        (by
          have h : (thetaAboveCell0000220030012302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012302 h)
        (by
          have h : (thetaAboveCell0000220030012303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030012310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012310 h)
        (by
          have h : (thetaAboveCell0000220030012311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012311 h)
        (by
          have h : (thetaAboveCell0000220030012312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012312 h)
        (by
          have h : (thetaAboveCell0000220030012313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030012313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022003001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022003001))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022003001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022003001))) h)

theorem cover_subtree_6705ea0fc5a0 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022003001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022003001)
    cover_subtree_6f0d223fa251
    cover_subtree_17de4b0fb6aa
    cover_subtree_2dc0f946809c
    cover_subtree_9ae7d1f286db

theorem cover_subtree_542c541386a0 :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022003001))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
    thetaAboveCell000022003001)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013020
        (by
          have h : ((childLL thetaAboveCell0000220030013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013020) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013020) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013020) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013021
        (by
          have h : ((childLL thetaAboveCell0000220030013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013021) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013021) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013021) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013022
        (by
          have h : ((childLL thetaAboveCell0000220030013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013022) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013022) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013022) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013023
        (by
          have h : ((childLL thetaAboveCell0000220030013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013023) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013023) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013023) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013023) h))

theorem cover_subtree_95991c39b4ae :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022003001))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
    thetaAboveCell000022003001)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013030
        (by
          have h : ((childLL thetaAboveCell0000220030013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013030) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013030) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013030) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013031
        (by
          have h : ((childLL thetaAboveCell0000220030013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013031) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013031) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013031) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013032
        (by
          have h : ((childLL thetaAboveCell0000220030013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013032) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013032) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013032) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013033
        (by
          have h : ((childLL thetaAboveCell0000220030013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013033) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013033) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013033) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013033) h))

theorem cover_subtree_f11aed5a1b39 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022003001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022003001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHH
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030013000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013000 h)
        (by
          have h : (thetaAboveCell0000220030013001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013001 h)
        (by
          have h : (thetaAboveCell0000220030013002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013002 h)
        (by
          have h : (thetaAboveCell0000220030013003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHH
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030013010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013010 h)
        (by
          have h : (thetaAboveCell0000220030013011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013011 h)
        (by
          have h : (thetaAboveCell0000220030013012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013012 h)
        (by
          have h : (thetaAboveCell0000220030013013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013013 h))
    cover_subtree_542c541386a0
    cover_subtree_95991c39b4ae

theorem cover_subtree_36cc60506fd2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022003001))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
    thetaAboveCell000022003001)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013120
        (by
          have h : ((childLL thetaAboveCell0000220030013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013120) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013120) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013120) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013121
        (by
          have h : ((childLL thetaAboveCell0000220030013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013121) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013121) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013121) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013122
        (by
          have h : ((childLL thetaAboveCell0000220030013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013122) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013122) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013122) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013123
        (by
          have h : ((childLL thetaAboveCell0000220030013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013123) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013123) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013123) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013123) h))

theorem cover_subtree_3db2622a8526 :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022003001))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
    thetaAboveCell000022003001)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013130
        (by
          have h : ((childLL thetaAboveCell0000220030013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013130) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013130) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013130) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013131
        (by
          have h : ((childLL thetaAboveCell0000220030013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013131) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013131) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013131) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013132
        (by
          have h : ((childLL thetaAboveCell0000220030013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013132) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013132) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013132) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030013133
        (by
          have h : ((childLL thetaAboveCell0000220030013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030013133) h)
        (by
          have h : ((childLH thetaAboveCell0000220030013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030013133) h)
        (by
          have h : ((childHL thetaAboveCell0000220030013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030013133) h)
        (by
          have h : ((childHH thetaAboveCell0000220030013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030013133) h))

theorem cover_subtree_13cfd42cc1e7 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022003001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022003001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHH
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030013100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013100 h)
        (by
          have h : (thetaAboveCell0000220030013101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013101 h)
        (by
          have h : (thetaAboveCell0000220030013102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013102 h)
        (by
          have h : (thetaAboveCell0000220030013103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHH
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030013110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013110 h)
        (by
          have h : (thetaAboveCell0000220030013111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013111 h)
        (by
          have h : (thetaAboveCell0000220030013112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013112 h)
        (by
          have h : (thetaAboveCell0000220030013113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013113 h))
    cover_subtree_36cc60506fd2
    cover_subtree_3db2622a8526

theorem cover_subtree_49af2ce5bec1 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022003001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022003001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030013200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013200 h)
        (by
          have h : (thetaAboveCell0000220030013201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013201 h)
        (by
          have h : (thetaAboveCell0000220030013202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013202 h)
        (by
          have h : (thetaAboveCell0000220030013203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030013210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013210 h)
        (by
          have h : (thetaAboveCell0000220030013211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013211 h)
        (by
          have h : (thetaAboveCell0000220030013212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013212 h)
        (by
          have h : (thetaAboveCell0000220030013213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022003001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022003001))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022003001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022003001))) h)

theorem cover_subtree_8008b2d13d89 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022003001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022003001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030013300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013300 h)
        (by
          have h : (thetaAboveCell0000220030013301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013301 h)
        (by
          have h : (thetaAboveCell0000220030013302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013302 h)
        (by
          have h : (thetaAboveCell0000220030013303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022003001)))
        (by
          have h : (thetaAboveCell0000220030013310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013310 h)
        (by
          have h : (thetaAboveCell0000220030013311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013311 h)
        (by
          have h : (thetaAboveCell0000220030013312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013312 h)
        (by
          have h : (thetaAboveCell0000220030013313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030013313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022003001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022003001))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022003001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022003001))) h)

theorem cover_subtree_bb781a080715 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022003001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022003001)
    cover_subtree_f11aed5a1b39
    cover_subtree_13cfd42cc1e7
    cover_subtree_49af2ce5bec1
    cover_subtree_8008b2d13d89

theorem cover_subtree_77cd353d9ac1 :
    adaptiveCoverCheck 7 thetaAboveCell000022003001 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003001
    cover_subtree_b0fbdd86b439
    cover_subtree_f6d73cfc8f96
    cover_subtree_6705ea0fc5a0
    cover_subtree_bb781a080715

theorem cover_subtree_728def59c89b :
    adaptiveCoverCheck 7 thetaAboveCell000022003002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003002
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003002)
        (by
          have h : ((childLL (childLL thetaAboveCell000022003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022003002)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022003002)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022003002)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022003002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003002)
        (by
          have h : ((childLL (childLH thetaAboveCell000022003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022003002)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022003002)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022003002)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022003002)) h))
    (by
      have h : ((childHL thetaAboveCell000022003002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022003002) h)
    (by
      have h : ((childHH thetaAboveCell000022003002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022003002) h)

theorem cover_subtree_14ed04390cca :
    adaptiveCoverCheck 7 thetaAboveCell000022003003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003003
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003003)
        (by
          have h : ((childLL (childLL thetaAboveCell000022003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022003003)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022003003)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022003003)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022003003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003003)
        (by
          have h : ((childLL (childLH thetaAboveCell000022003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022003003)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022003003)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022003003)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022003003)) h))
    (by
      have h : ((childHL thetaAboveCell000022003003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022003003) h)
    (by
      have h : ((childHH thetaAboveCell000022003003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022003003) h)

theorem cover_subtree_f2d4d32c5725 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00002200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00002200)))
    cover_subtree_df29b2bfe6c5
    cover_subtree_77cd353d9ac1
    cover_subtree_728def59c89b
    cover_subtree_14ed04390cca

theorem cover_subtree_6de0f218ce5a :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022003010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003010)
    (by
      have h : ((childLL (childLL thetaAboveCell000022003010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL thetaAboveCell000022003010)) h)
    (by
      have h : ((childLH (childLL thetaAboveCell000022003010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL thetaAboveCell000022003010)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022003010))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022003010))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022003010))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022003010))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022003010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022003010))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022003010))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022003010))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022003010))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022003010))) h))

theorem cover_subtree_09a87211ea0e :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022003010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003010)
    (by
      have h : ((childLL (childLH thetaAboveCell000022003010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH thetaAboveCell000022003010)) h)
    (by
      have h : ((childLH (childLH thetaAboveCell000022003010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH thetaAboveCell000022003010)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022003010))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022003010))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022003010))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022003010))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022003010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022003010))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022003010))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022003010))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022003010))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022003010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022003010))) h))

theorem cover_subtree_1222a4bbaf46 :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022003010))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
    thetaAboveCell000022003010)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102020
        (by
          have h : ((childLL thetaAboveCell0000220030102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102020) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102020) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102020) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102021
        (by
          have h : ((childLL thetaAboveCell0000220030102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102021) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102021) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102021) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102022
        (by
          have h : ((childLL thetaAboveCell0000220030102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102022) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102022) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102022) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102023
        (by
          have h : ((childLL thetaAboveCell0000220030102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102023) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102023) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102023) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102023) h))

theorem cover_subtree_f813068a0ab7 :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022003010))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
    thetaAboveCell000022003010)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102030
        (by
          have h : ((childLL thetaAboveCell0000220030102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102030) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102030) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102030) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102031
        (by
          have h : ((childLL thetaAboveCell0000220030102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102031) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102031) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102031) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102032
        (by
          have h : ((childLL thetaAboveCell0000220030102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102032) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102032) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102032) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102033
        (by
          have h : ((childLL thetaAboveCell0000220030102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102033) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102033) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102033) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102033) h))

theorem cover_subtree_4a16ed9c24b8 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022003010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022003010))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL
        thetaAboveCell000022003010)))
        (by
          have h : (thetaAboveCell0000220030102000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102000 h)
        (by
          have h : (thetaAboveCell0000220030102001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102001 h)
        (by
          have h : (thetaAboveCell0000220030102002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102002 h)
        (by
          have h : (thetaAboveCell0000220030102003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL
        thetaAboveCell000022003010)))
        (by
          have h : (thetaAboveCell0000220030102010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102010 h)
        (by
          have h : (thetaAboveCell0000220030102011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102011 h)
        (by
          have h : (thetaAboveCell0000220030102012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102012 h)
        (by
          have h : (thetaAboveCell0000220030102013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102013 h))
    cover_subtree_1222a4bbaf46
    cover_subtree_f813068a0ab7

theorem cover_subtree_f9b60e2c6701 :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022003010))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
    thetaAboveCell000022003010)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102120
        (by
          have h : ((childLL thetaAboveCell0000220030102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102120) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102120) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102120) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102121
        (by
          have h : ((childLL thetaAboveCell0000220030102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102121) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102121) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102121) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102122
        (by
          have h : ((childLL thetaAboveCell0000220030102122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102122) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102122) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102122) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102123
        (by
          have h : ((childLL thetaAboveCell0000220030102123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102123) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102123) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102123) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102123) h))

theorem cover_subtree_ccf472fb2f11 :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022003010))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
    thetaAboveCell000022003010)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102130
        (by
          have h : ((childLL thetaAboveCell0000220030102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102130) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102130) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102130) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102131
        (by
          have h : ((childLL thetaAboveCell0000220030102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102131) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102131) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102131) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102132
        (by
          have h : ((childLL thetaAboveCell0000220030102132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102132) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102132) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102132) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030102133
        (by
          have h : ((childLL thetaAboveCell0000220030102133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030102133) h)
        (by
          have h : ((childLH thetaAboveCell0000220030102133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030102133) h)
        (by
          have h : ((childHL thetaAboveCell0000220030102133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030102133) h)
        (by
          have h : ((childHH thetaAboveCell0000220030102133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030102133) h))

theorem cover_subtree_7315e35a4c15 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022003010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022003010))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL
        thetaAboveCell000022003010)))
        (by
          have h : (thetaAboveCell0000220030102100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102100 h)
        (by
          have h : (thetaAboveCell0000220030102101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102101 h)
        (by
          have h : (thetaAboveCell0000220030102102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102102 h)
        (by
          have h : (thetaAboveCell0000220030102103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHL
        thetaAboveCell000022003010)))
        (by
          have h : (thetaAboveCell0000220030102110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102110 h)
        (by
          have h : (thetaAboveCell0000220030102111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102111 h)
        (by
          have h : (thetaAboveCell0000220030102112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102112 h)
        (by
          have h : (thetaAboveCell0000220030102113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102113 h))
    cover_subtree_f9b60e2c6701
    cover_subtree_ccf472fb2f11

theorem cover_subtree_5d09bb0853a8 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022003010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022003010))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022003010)))
        (by
          have h : (thetaAboveCell0000220030102200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102200 h)
        (by
          have h : (thetaAboveCell0000220030102201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102201 h)
        (by
          have h : (thetaAboveCell0000220030102202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102202 h)
        (by
          have h : (thetaAboveCell0000220030102203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022003010)))
        (by
          have h : (thetaAboveCell0000220030102210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102210 h)
        (by
          have h : (thetaAboveCell0000220030102211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102211 h)
        (by
          have h : (thetaAboveCell0000220030102212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102212 h)
        (by
          have h : (thetaAboveCell0000220030102213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022003010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022003010))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022003010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022003010))) h)

theorem cover_subtree_b82287a58720 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022003010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022003010))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022003010)))
        (by
          have h : (thetaAboveCell0000220030102300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102300 h)
        (by
          have h : (thetaAboveCell0000220030102301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102301 h)
        (by
          have h : (thetaAboveCell0000220030102302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102302 h)
        (by
          have h : (thetaAboveCell0000220030102303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022003010)))
        (by
          have h : (thetaAboveCell0000220030102310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102310 h)
        (by
          have h : (thetaAboveCell0000220030102311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102311 h)
        (by
          have h : (thetaAboveCell0000220030102312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102312 h)
        (by
          have h : (thetaAboveCell0000220030102313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030102313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022003010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022003010))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022003010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022003010))) h)

theorem cover_subtree_8668bec96df6 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022003010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022003010)
    cover_subtree_4a16ed9c24b8
    cover_subtree_7315e35a4c15
    cover_subtree_5d09bb0853a8
    cover_subtree_b82287a58720

theorem cover_subtree_f7763668c82e :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022003010))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
    thetaAboveCell000022003010)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103020
        (by
          have h : ((childLL thetaAboveCell0000220030103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103020) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103020) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103020) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103021
        (by
          have h : ((childLL thetaAboveCell0000220030103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103021) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103021) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103021) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103022
        (by
          have h : ((childLL thetaAboveCell0000220030103022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103022) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103022) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103022) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103023
        (by
          have h : ((childLL thetaAboveCell0000220030103023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103023) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103023) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103023) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103023) h))

theorem cover_subtree_8b7188d14517 :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022003010))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
    thetaAboveCell000022003010)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103030
        (by
          have h : ((childLL thetaAboveCell0000220030103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103030) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103030) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103030) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103031
        (by
          have h : ((childLL thetaAboveCell0000220030103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103031) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103031) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103031) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103032
        (by
          have h : ((childLL thetaAboveCell0000220030103032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103032) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103032) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103032) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103033
        (by
          have h : ((childLL thetaAboveCell0000220030103033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103033) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103033) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103033) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103033) h))

theorem cover_subtree_7cb6055f8e6a :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022003010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022003010))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHH
        thetaAboveCell000022003010)))
        (by
          have h : (thetaAboveCell0000220030103000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103000 h)
        (by
          have h : (thetaAboveCell0000220030103001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103001 h)
        (by
          have h : (thetaAboveCell0000220030103002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103002 h)
        (by
          have h : (thetaAboveCell0000220030103003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHH
        thetaAboveCell000022003010)))
        (by
          have h : (thetaAboveCell0000220030103010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103010 h)
        (by
          have h : (thetaAboveCell0000220030103011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103011 h)
        (by
          have h : (thetaAboveCell0000220030103012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103012 h)
        (by
          have h : (thetaAboveCell0000220030103013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103013 h))
    cover_subtree_f7763668c82e
    cover_subtree_8b7188d14517

theorem cover_subtree_d99c2055d296 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022003010))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
    thetaAboveCell000022003010)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103120
        (by
          have h : ((childLL thetaAboveCell0000220030103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103120) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103120) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103120) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103121
        (by
          have h : ((childLL thetaAboveCell0000220030103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103121) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103121) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103121) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103122
        (by
          have h : ((childLL thetaAboveCell0000220030103122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103122) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103122) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103122) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103123
        (by
          have h : ((childLL thetaAboveCell0000220030103123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103123) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103123) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103123) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103123) h))

theorem cover_subtree_a6b3a4adb113 :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022003010))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
    thetaAboveCell000022003010)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103130
        (by
          have h : ((childLL thetaAboveCell0000220030103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103130) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103130) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103130) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103131
        (by
          have h : ((childLL thetaAboveCell0000220030103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103131) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103131) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103131) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103132
        (by
          have h : ((childLL thetaAboveCell0000220030103132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103132) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103132) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103132) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103133
        (by
          have h : ((childLL thetaAboveCell0000220030103133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103133) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103133) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103133) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103133) h))

theorem cover_subtree_b64accded341 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022003010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022003010))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHH
        thetaAboveCell000022003010)))
        (by
          have h : (thetaAboveCell0000220030103100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103100 h)
        (by
          have h : (thetaAboveCell0000220030103101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103101 h)
        (by
          have h : (thetaAboveCell0000220030103102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103102 h)
        (by
          have h : (thetaAboveCell0000220030103103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHH
        thetaAboveCell000022003010)))
        (by
          have h : (thetaAboveCell0000220030103110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103110 h)
        (by
          have h : (thetaAboveCell0000220030103111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103111 h)
        (by
          have h : (thetaAboveCell0000220030103112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103112 h)
        (by
          have h : (thetaAboveCell0000220030103113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103113 h))
    cover_subtree_d99c2055d296
    cover_subtree_a6b3a4adb113

theorem cover_subtree_cf9e35b58ea8 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022003010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022003010))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022003010)))
        (by
          have h : (thetaAboveCell0000220030103200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103200 h)
        (by
          have h : (thetaAboveCell0000220030103201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103201 h)
        (by
          have h : (thetaAboveCell0000220030103202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103202 h)
        (by
          have h : (thetaAboveCell0000220030103203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022003010)))
        (by
          have h : (thetaAboveCell0000220030103210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103210 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103211
            (by
              have h : ((childLL thetaAboveCell0000220030103211)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103211)
                h)
            (by
              have h : ((childLH thetaAboveCell0000220030103211)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103211)
                h)
            (by
              have h : ((childHL thetaAboveCell0000220030103211)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103211)
                h)
            (by
              have h : ((childHH thetaAboveCell0000220030103211)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103211)
                h))
        (by
          have h : (thetaAboveCell0000220030103212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103212 h)
        (by
          have h : (thetaAboveCell0000220030103213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022003010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022003010))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022003010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022003010))) h)

theorem cover_subtree_f351407ea291 :
    adaptiveCoverCheck 4 (childLL (childHH (childHH thetaAboveCell000022003010))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
    thetaAboveCell000022003010)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103300
        (by
          have h : ((childLL thetaAboveCell0000220030103300)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103300) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103300)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103300) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103300)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103300) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103300)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103300) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103301
        (by
          have h : ((childLL thetaAboveCell0000220030103301)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103301) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103301)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103301) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103301)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103301) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103301)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103301) h))
    (by
      have h : (thetaAboveCell0000220030103302).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103302 h)
    (by
      have h : (thetaAboveCell0000220030103303).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103303 h)

theorem cover_subtree_0ec74c623b25 :
    adaptiveCoverCheck 4 (childLH (childHH (childHH thetaAboveCell000022003010))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
    thetaAboveCell000022003010)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103310
        (by
          have h : ((childLL thetaAboveCell0000220030103310)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103310) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103310)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103310) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103310)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103310) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103310)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103310) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030103311
        (by
          have h : ((childLL thetaAboveCell0000220030103311)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030103311) h)
        (by
          have h : ((childLH thetaAboveCell0000220030103311)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030103311) h)
        (by
          have h : ((childHL thetaAboveCell0000220030103311)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030103311) h)
        (by
          have h : ((childHH thetaAboveCell0000220030103311)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030103311) h))
    (by
      have h : (thetaAboveCell0000220030103312).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103312 h)
    (by
      have h : (thetaAboveCell0000220030103313).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030103313 h)

theorem cover_subtree_5b0864ff4bca :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022003010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022003010))
    cover_subtree_f351407ea291
    cover_subtree_0ec74c623b25
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022003010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022003010))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022003010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022003010))) h)

theorem cover_subtree_deeae114ec93 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022003010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022003010)
    cover_subtree_7cb6055f8e6a
    cover_subtree_b64accded341
    cover_subtree_cf9e35b58ea8
    cover_subtree_5b0864ff4bca

theorem cover_subtree_591cadb839e1 :
    adaptiveCoverCheck 7 thetaAboveCell000022003010 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003010
    cover_subtree_6de0f218ce5a
    cover_subtree_09a87211ea0e
    cover_subtree_8668bec96df6
    cover_subtree_deeae114ec93

theorem cover_subtree_30fdf3821f37 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022003011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003011)
    (by
      have h : ((childLL (childLL thetaAboveCell000022003011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL thetaAboveCell000022003011)) h)
    (by
      have h : ((childLH (childLL thetaAboveCell000022003011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL thetaAboveCell000022003011)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022003011))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022003011))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022003011))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022003011))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022003011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022003011))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022003011))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022003011))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022003011))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022003011))) h))

theorem cover_subtree_c04a84ca091e :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022003011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003011)
    (by
      have h : ((childLL (childLH thetaAboveCell000022003011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH thetaAboveCell000022003011)) h)
    (by
      have h : ((childLH (childLH thetaAboveCell000022003011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH thetaAboveCell000022003011)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022003011))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022003011))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022003011))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022003011))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022003011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022003011))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022003011))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022003011))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022003011))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022003011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022003011))) h))

theorem cover_subtree_665b5a9e2762 :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112020
        (by
          have h : ((childLL thetaAboveCell0000220030112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112020) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112020) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112020) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112021
        (by
          have h : ((childLL thetaAboveCell0000220030112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112021) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112021) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112021) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112022
        (by
          have h : ((childLL thetaAboveCell0000220030112022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112022) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112022) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112022) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112023
        (by
          have h : ((childLL thetaAboveCell0000220030112023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112023) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112023) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112023) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112023) h))

theorem cover_subtree_5b6db01eac76 :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112030
        (by
          have h : ((childLL thetaAboveCell0000220030112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112030) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112030) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112030) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112031
        (by
          have h : ((childLL thetaAboveCell0000220030112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112031) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112031) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112031) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112032
        (by
          have h : ((childLL thetaAboveCell0000220030112032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112032) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112032) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112032) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112033
        (by
          have h : ((childLL thetaAboveCell0000220030112033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112033) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112033) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112033) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112033) h))

theorem cover_subtree_f193f827132f :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022003011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022003011))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL
        thetaAboveCell000022003011)))
        (by
          have h : (thetaAboveCell0000220030112000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112000 h)
        (by
          have h : (thetaAboveCell0000220030112001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112001 h)
        (by
          have h : (thetaAboveCell0000220030112002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112002 h)
        (by
          have h : (thetaAboveCell0000220030112003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL
        thetaAboveCell000022003011)))
        (by
          have h : (thetaAboveCell0000220030112010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112010 h)
        (by
          have h : (thetaAboveCell0000220030112011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112011 h)
        (by
          have h : (thetaAboveCell0000220030112012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112012 h)
        (by
          have h : (thetaAboveCell0000220030112013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112013 h))
    cover_subtree_665b5a9e2762
    cover_subtree_5b6db01eac76

theorem cover_subtree_852b952eb7f8 :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112120
        (by
          have h : ((childLL thetaAboveCell0000220030112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112120) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112120) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112120) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112121
        (by
          have h : ((childLL thetaAboveCell0000220030112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112121) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112121) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112121) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112122
        (by
          have h : ((childLL thetaAboveCell0000220030112122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112122) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112122) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112122) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112123
        (by
          have h : ((childLL thetaAboveCell0000220030112123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112123) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112123) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112123) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112123) h))

theorem cover_subtree_aaaee1c4417b :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112130
        (by
          have h : ((childLL thetaAboveCell0000220030112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112130) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112130) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112130) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112131
        (by
          have h : ((childLL thetaAboveCell0000220030112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112131) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112131) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112131) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112132
        (by
          have h : ((childLL thetaAboveCell0000220030112132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112132) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112132) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112132) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112133
        (by
          have h : ((childLL thetaAboveCell0000220030112133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112133) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112133) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112133) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112133) h))

theorem cover_subtree_351a53bd4fd0 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022003011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022003011))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL
        thetaAboveCell000022003011)))
        (by
          have h : (thetaAboveCell0000220030112100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112100 h)
        (by
          have h : (thetaAboveCell0000220030112101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112101 h)
        (by
          have h : (thetaAboveCell0000220030112102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112102 h)
        (by
          have h : (thetaAboveCell0000220030112103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHL
        thetaAboveCell000022003011)))
        (by
          have h : (thetaAboveCell0000220030112110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112110 h)
        (by
          have h : (thetaAboveCell0000220030112111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112111 h)
        (by
          have h : (thetaAboveCell0000220030112112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112112 h)
        (by
          have h : (thetaAboveCell0000220030112113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112113 h))
    cover_subtree_852b952eb7f8
    cover_subtree_aaaee1c4417b

theorem cover_subtree_272316153167 :
    adaptiveCoverCheck 4 (childLL (childHL (childHL thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112200
        (by
          have h : ((childLL thetaAboveCell0000220030112200)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112200) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112200)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112200) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112200)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112200) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112200)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112200) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112201
        (by
          have h : ((childLL thetaAboveCell0000220030112201)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112201) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112201)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112201) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112201)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112201) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112201)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112201) h))
    (by
      have h : (thetaAboveCell0000220030112202).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112202 h)
    (by
      have h : (thetaAboveCell0000220030112203).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112203 h)

theorem cover_subtree_665ac8a38e4e :
    adaptiveCoverCheck 4 (childLH (childHL (childHL thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112210
        (by
          have h : ((childLL thetaAboveCell0000220030112210)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112210) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112210)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112210) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112210)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112210) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112210)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112210) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112211
        (by
          have h : ((childLL thetaAboveCell0000220030112211)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112211) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112211)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112211) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112211)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112211) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112211)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112211) h))
    (by
      have h : (thetaAboveCell0000220030112212).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112212 h)
    (by
      have h : (thetaAboveCell0000220030112213).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112213 h)

theorem cover_subtree_53d66be9fa12 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022003011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022003011))
    cover_subtree_272316153167
    cover_subtree_665ac8a38e4e
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022003011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022003011))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022003011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022003011))) h)

theorem cover_subtree_173035df5204 :
    adaptiveCoverCheck 4 (childLL (childHH (childHL thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112300
        (by
          have h : ((childLL thetaAboveCell0000220030112300)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112300) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112300)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112300) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112300)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112300) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112300)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112300) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112301
        (by
          have h : ((childLL thetaAboveCell0000220030112301)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112301) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112301)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112301) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112301)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112301) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112301)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112301) h))
    (by
      have h : (thetaAboveCell0000220030112302).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112302 h)
    (by
      have h : (thetaAboveCell0000220030112303).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112303 h)

theorem cover_subtree_9b2979ef98c7 :
    adaptiveCoverCheck 4 (childLH (childHH (childHL thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112310
        (by
          have h : ((childLL thetaAboveCell0000220030112310)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112310) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112310)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112310) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112310)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112310) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112310)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112310) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030112311
        (by
          have h : ((childLL thetaAboveCell0000220030112311)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030112311) h)
        (by
          have h : ((childLH thetaAboveCell0000220030112311)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030112311) h)
        (by
          have h : ((childHL thetaAboveCell0000220030112311)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030112311) h)
        (by
          have h : ((childHH thetaAboveCell0000220030112311)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030112311) h))
    (by
      have h : (thetaAboveCell0000220030112312).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112312 h)
    (by
      have h : (thetaAboveCell0000220030112313).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030112313 h)

theorem cover_subtree_c1dab1b76c15 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022003011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022003011))
    cover_subtree_173035df5204
    cover_subtree_9b2979ef98c7
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022003011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022003011))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022003011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022003011))) h)

theorem cover_subtree_7f164fbda87a :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022003011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022003011)
    cover_subtree_f193f827132f
    cover_subtree_351a53bd4fd0
    cover_subtree_53d66be9fa12
    cover_subtree_c1dab1b76c15

theorem cover_subtree_45ff29f15e49 :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113020
        (by
          have h : ((childLL thetaAboveCell0000220030113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113020) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113020) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113020) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113021
        (by
          have h : ((childLL thetaAboveCell0000220030113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113021) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113021) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113021) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113022
        (by
          have h : ((childLL thetaAboveCell0000220030113022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113022) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113022) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113022) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113023
        (by
          have h : ((childLL thetaAboveCell0000220030113023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113023) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113023) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113023) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113023) h))

theorem cover_subtree_2ca50076570c :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113030
        (by
          have h : ((childLL thetaAboveCell0000220030113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113030) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113030) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113030) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113031
        (by
          have h : ((childLL thetaAboveCell0000220030113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113031) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113031) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113031) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113032
        (by
          have h : ((childLL thetaAboveCell0000220030113032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113032) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113032) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113032) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113033
        (by
          have h : ((childLL thetaAboveCell0000220030113033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113033) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113033) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113033) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113033) h))

theorem cover_subtree_6cee8ff9ebee :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022003011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022003011))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHH
        thetaAboveCell000022003011)))
        (by
          have h : (thetaAboveCell0000220030113000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113000 h)
        (by
          have h : (thetaAboveCell0000220030113001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113001 h)
        (by
          have h : (thetaAboveCell0000220030113002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113002 h)
        (by
          have h : (thetaAboveCell0000220030113003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHH
        thetaAboveCell000022003011)))
        (by
          have h : (thetaAboveCell0000220030113010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113010 h)
        (by
          have h : (thetaAboveCell0000220030113011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113011 h)
        (by
          have h : (thetaAboveCell0000220030113012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113012 h)
        (by
          have h : (thetaAboveCell0000220030113013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113013 h))
    cover_subtree_45ff29f15e49
    cover_subtree_2ca50076570c

theorem cover_subtree_ce8d22ab5f51 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113120
        (by
          have h : ((childLL thetaAboveCell0000220030113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113120) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113120) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113120) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113121
        (by
          have h : ((childLL thetaAboveCell0000220030113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113121) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113121) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113121) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113122
        (by
          have h : ((childLL thetaAboveCell0000220030113122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113122) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113122) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113122) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113123
        (by
          have h : ((childLL thetaAboveCell0000220030113123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113123) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113123) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113123) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113123) h))

theorem cover_subtree_23abbb95182b :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113130
        (by
          have h : ((childLL thetaAboveCell0000220030113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113130) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113130) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113130) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113131
        (by
          have h : ((childLL thetaAboveCell0000220030113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113131) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113131) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113131) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113132
        (by
          have h : ((childLL thetaAboveCell0000220030113132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113132) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113132) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113132) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113133
        (by
          have h : ((childLL thetaAboveCell0000220030113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113133) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113133) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113133) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113133) h))

theorem cover_subtree_7ed35f4a5f6c :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022003011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022003011))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHH
        thetaAboveCell000022003011)))
        (by
          have h : (thetaAboveCell0000220030113100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113100 h)
        (by
          have h : (thetaAboveCell0000220030113101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113101 h)
        (by
          have h : (thetaAboveCell0000220030113102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113102 h)
        (by
          have h : (thetaAboveCell0000220030113103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHH
        thetaAboveCell000022003011)))
        (by
          have h : (thetaAboveCell0000220030113110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113110 h)
        (by
          have h : (thetaAboveCell0000220030113111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113111 h)
        (by
          have h : (thetaAboveCell0000220030113112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113112 h)
        (by
          have h : (thetaAboveCell0000220030113113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113113 h))
    cover_subtree_ce8d22ab5f51
    cover_subtree_23abbb95182b

theorem cover_subtree_c767073053c7 :
    adaptiveCoverCheck 4 (childLL (childHL (childHH thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113200
        (by
          have h : ((childLL thetaAboveCell0000220030113200)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113200) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113200)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113200) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113200)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113200) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113200)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113200) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113201
        (by
          have h : ((childLL thetaAboveCell0000220030113201)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113201) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113201)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113201) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113201)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113201) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113201)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113201) h))
    (by
      have h : (thetaAboveCell0000220030113202).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113202 h)
    (by
      have h : (thetaAboveCell0000220030113203).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113203 h)

theorem cover_subtree_76bb187113c3 :
    adaptiveCoverCheck 4 (childLH (childHL (childHH thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113210
        (by
          have h : ((childLL thetaAboveCell0000220030113210)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113210) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113210)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113210) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113210)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113210) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113210)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113210) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113211
        (by
          have h : ((childLL thetaAboveCell0000220030113211)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113211) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113211)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113211) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113211)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113211) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113211)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113211) h))
    (by
      have h : (thetaAboveCell0000220030113212).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113212 h)
    (by
      have h : (thetaAboveCell0000220030113213).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113213 h)

theorem cover_subtree_9060e2b44288 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022003011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022003011))
    cover_subtree_c767073053c7
    cover_subtree_76bb187113c3
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022003011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022003011))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022003011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022003011))) h)

theorem cover_subtree_15620f5ff6d8 :
    adaptiveCoverCheck 4 (childLL (childHH (childHH thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113300
        (by
          have h : ((childLL thetaAboveCell0000220030113300)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113300) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113300)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113300) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113300)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113300) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113300)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113300) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113301
        (by
          have h : ((childLL thetaAboveCell0000220030113301)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113301) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113301)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113301) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113301)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113301) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113301)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113301) h))
    (by
      have h : (thetaAboveCell0000220030113302).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113302 h)
    (by
      have h : (thetaAboveCell0000220030113303).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113303 h)

theorem cover_subtree_4b9adb2a2d0e :
    adaptiveCoverCheck 4 (childLH (childHH (childHH thetaAboveCell000022003011))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
    thetaAboveCell000022003011)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113310
        (by
          have h : ((childLL thetaAboveCell0000220030113310)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113310) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113310)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113310) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113310)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113310) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113310)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113310) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220030113311
        (by
          have h : ((childLL thetaAboveCell0000220030113311)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220030113311) h)
        (by
          have h : ((childLH thetaAboveCell0000220030113311)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220030113311) h)
        (by
          have h : ((childHL thetaAboveCell0000220030113311)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220030113311) h)
        (by
          have h : ((childHH thetaAboveCell0000220030113311)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220030113311) h))
    (by
      have h : (thetaAboveCell0000220030113312).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113312 h)
    (by
      have h : (thetaAboveCell0000220030113313).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220030113313 h)

theorem cover_subtree_92d2cedcde3a :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022003011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022003011))
    cover_subtree_15620f5ff6d8
    cover_subtree_4b9adb2a2d0e
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022003011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022003011))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022003011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022003011))) h)

theorem cover_subtree_f164ca59fbf6 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022003011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022003011)
    cover_subtree_6cee8ff9ebee
    cover_subtree_7ed35f4a5f6c
    cover_subtree_9060e2b44288
    cover_subtree_92d2cedcde3a

theorem cover_subtree_a889ceb5a59d :
    adaptiveCoverCheck 7 thetaAboveCell000022003011 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003011
    cover_subtree_30fdf3821f37
    cover_subtree_c04a84ca091e
    cover_subtree_7f164fbda87a
    cover_subtree_f164ca59fbf6

theorem cover_subtree_258ec0944afe :
    adaptiveCoverCheck 7 thetaAboveCell000022003012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003012
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003012)
        (by
          have h : ((childLL (childLL thetaAboveCell000022003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022003012)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022003012)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022003012)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022003012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003012)
        (by
          have h : ((childLL (childLH thetaAboveCell000022003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022003012)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022003012)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022003012)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022003012)) h))
    (by
      have h : ((childHL thetaAboveCell000022003012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022003012) h)
    (by
      have h : ((childHH thetaAboveCell000022003012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022003012) h)

theorem cover_subtree_935d1978c95d :
    adaptiveCoverCheck 7 thetaAboveCell000022003013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003013
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003013)
        (by
          have h : ((childLL (childLL thetaAboveCell000022003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022003013)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022003013)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022003013)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022003013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003013)
        (by
          have h : ((childLL (childLH thetaAboveCell000022003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022003013)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022003013)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022003013)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022003013)) h))
    (by
      have h : ((childHL thetaAboveCell000022003013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022003013) h)
    (by
      have h : ((childHH thetaAboveCell000022003013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022003013) h)

theorem cover_subtree_53052734842a :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00002200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00002200)))
    cover_subtree_591cadb839e1
    cover_subtree_a889ceb5a59d
    cover_subtree_258ec0944afe
    cover_subtree_935d1978c95d

theorem e24KC2ThetaAboveLeaf0000220030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00002200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00002200))
    cover_subtree_f2d4d32c5725
    cover_subtree_53052734842a
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00002200)))
        (by
          have h : (thetaAboveCell000022003020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003020 h)
        (by
          have h : (thetaAboveCell000022003021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003021 h)
        (by
          have h : (thetaAboveCell000022003022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003022 h)
        (by
          have h : (thetaAboveCell000022003023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00002200)))
        (by
          have h : (thetaAboveCell000022003030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003030 h)
        (by
          have h : (thetaAboveCell000022003031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003031 h)
        (by
          have h : (thetaAboveCell000022003032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003032 h)
        (by
          have h : (thetaAboveCell000022003033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003033 h))

end PartE
end GerverSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.ThetaAbove.Leaf00642`.
* `KernelOnly.PartE.ThetaAbove.Leaf00643`.
* `KernelOnly.PartE.ThetaAbove.Leaf00646`.
* `KernelOnly.PartE.ThetaAbove.Leaf00647`.
* `KernelOnly.PartE.ThetaAbove.Leaf00648`.
* `KernelOnly.PartE.ThetaAbove.Leaf00649`.
* `KernelOnly.PartE.ThetaAbove.Leaf00652`.
* `KernelOnly.PartE.ThetaAbove.Leaf00653`.
* `KernelOnly.PartE.ThetaAbove.Leaf00654`.
* `KernelOnly.PartE.ThetaAbove.Leaf00655`.
* `KernelOnly.PartE.ThetaAbove.Leaf00657`.
* `KernelOnly.PartE.ThetaAbove.Leaf00658`.
* `KernelOnly.PartE.ThetaAbove.Leaf00662`.
* `KernelOnly.PartE.ThetaAbove.Leaf00663`.
* `KernelOnly.PartE.ThetaAbove.Leaf00664`.
* `KernelOnly.PartE.ThetaAbove.Leaf00665`.
-/

public section

noncomputable section

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c0_6_00642
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5e16eb2f1b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells5e16eb2f1b

open CertificateCells5e16eb2f1b
namespace CoverCertificate1bb21a49a4

private theorem checked20 : adaptiveCoverCheck 4 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 4 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 4 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 4 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 4 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 4 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 4 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 4 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 5 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 5 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 5 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 5 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 6 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate1bb21a49a4

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c0 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022002011) = true := by
  exact CoverCertificate1bb21a49a4.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c1_6_00643
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb7fa51f50b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsb7fa51f50b

open CertificateCellsb7fa51f50b
namespace CoverCertificatec9db3a1aba

private theorem checked20 : adaptiveCoverCheck 4 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 4 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 4 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 4 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 4 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 4 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 4 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 4 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 5 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 5 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 5 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 5 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 6 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatec9db3a1aba

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c1 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022002011) = true := by
  exact CoverCertificatec9db3a1aba.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c2_c0_c0_4_00646
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd618452127

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsd618452127

open CertificateCellsd618452127
namespace CoverCertificatefb03004e1f

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatefb03004e1f

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c0_c0 :
    adaptiveCoverCheck 4 (childLL (childLL (childHL thetaAboveCell000022002011))) = true := by
  exact CoverCertificatefb03004e1f.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c2_c0_c1_4_00647
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells82d3525350

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells82d3525350

open CertificateCells82d3525350
namespace CoverCertificate045cecfd86

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate045cecfd86

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c0_c1 :
    adaptiveCoverCheck 4 (childLH (childLL (childHL thetaAboveCell000022002011))) = true := by
  exact CoverCertificate045cecfd86.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c2_c0_c2_4_00648
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells632f810978

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells632f810978

open CertificateCells632f810978
namespace CoverCertificatef837300024

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatef837300024

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c0_c2 :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022002011))) = true := by
  exact CoverCertificatef837300024.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c2_c0_c3_4_00649
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells15b8174174

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells15b8174174

open CertificateCells15b8174174
namespace CoverCertificate2943ba0b5c

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate2943ba0b5c

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c0_c3 :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022002011))) = true := by
  exact CoverCertificate2943ba0b5c.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c2_c1_c0_4_00652
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1f25007fe8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells1f25007fe8

open CertificateCells1f25007fe8
namespace CoverCertificate42a60e756f

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate42a60e756f

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c1_c0 :
    adaptiveCoverCheck 4 (childLL (childLH (childHL thetaAboveCell000022002011))) = true := by
  exact CoverCertificate42a60e756f.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c2_c1_c1_4_00653
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1e9acaa8be

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells1e9acaa8be

open CertificateCells1e9acaa8be
namespace CoverCertificate0cee658f4b

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate0cee658f4b

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c1_c1 :
    adaptiveCoverCheck 4 (childLH (childLH (childHL thetaAboveCell000022002011))) = true := by
  exact CoverCertificate0cee658f4b.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c2_c1_c2_4_00654
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells231d66ab0c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells231d66ab0c

open CertificateCells231d66ab0c
namespace CoverCertificateeb376f6b8e

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateeb376f6b8e

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c1_c2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022002011))) = true := by
  exact CoverCertificateeb376f6b8e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c2_c1_c3_4_00655
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2c11250698

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells2c11250698

open CertificateCells2c11250698
namespace CoverCertificate1e208f1b6e

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate1e208f1b6e

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c1_c3 :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022002011))) = true := by
  exact CoverCertificate1e208f1b6e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c2_c2_5_00657
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3ce31f23ce

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells3ce31f23ce

open CertificateCells3ce31f23ce
namespace CoverCertificate6fd62aabed

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate6fd62aabed

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c2 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022002011)) = true := by
  exact CoverCertificate6fd62aabed.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c2_c3_5_00658
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3c3d48c1eb

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells3c3d48c1eb

open CertificateCells3c3d48c1eb
namespace CoverCertificate22515ac7bd

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate22515ac7bd

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c3 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022002011)) = true := by
  exact CoverCertificate22515ac7bd.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c0_c0_4_00662
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4d022b961f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells4d022b961f

open CertificateCells4d022b961f
namespace CoverCertificatebad9a9b575

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatebad9a9b575

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c0_c0 :
    adaptiveCoverCheck 4 (childLL (childLL (childHH thetaAboveCell000022002011))) = true := by
  exact CoverCertificatebad9a9b575.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c0_c1_4_00663
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9798c9c840

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells9798c9c840

open CertificateCells9798c9c840
namespace CoverCertificate13a680926b

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate13a680926b

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c0_c1 :
    adaptiveCoverCheck 4 (childLH (childLL (childHH thetaAboveCell000022002011))) = true := by
  exact CoverCertificate13a680926b.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c0_c2_4_00664
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6832cee036

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells6832cee036

open CertificateCells6832cee036
namespace CoverCertificatebdefa88d14

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatebdefa88d14

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c0_c2 :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022002011))) = true := by
  exact CoverCertificatebdefa88d14.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c0_c3_4_00665
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsab896aa443

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsab896aa443

open CertificateCellsab896aa443
namespace CoverCertificateb54a5d06ec

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateb54a5d06ec

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c0_c3 :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022002011))) = true := by
  exact CoverCertificateb54a5d06ec.checkedRoot

end PartE
end GerverSofa

end

end

end

end

end

end
