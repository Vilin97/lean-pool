/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle001
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle002
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle003

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle004
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle005
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle006
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle007
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle008
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle009
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle010



public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle011

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle012
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle013

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle014

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle015


public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle016




public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle017
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle018
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle019
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle020
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle021
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle022
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle023
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle024
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle025
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle026
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle027
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle028
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle029


public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle007
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Reconstruction`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCells6754c8bb3e

/-- Subcell `1101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1011 : AngleCell :=
  childLH (childLH (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1100 : AngleCell :=
  childLL (childLL (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1001 : AngleCell :=
  childLH (childLL (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1010 : AngleCell :=
  childLL (childLH (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1112 : AngleCell :=
  childHL (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1113 : AngleCell :=
  childHH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `0101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0101 : AngleCell :=
  childLH (childLL (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0110 : AngleCell :=
  childLL (childLH (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0111 : AngleCell :=
  childLH (childLH (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `1000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1000 : AngleCell :=
  childLL (childLL (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1003 : AngleCell :=
  childHH (childLL (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1012 : AngleCell :=
  childHL (childLH (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1013 : AngleCell :=
  childHH (childLH (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1102 : AngleCell :=
  childHL (childLL (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1103 : AngleCell :=
  childHH (childLL (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `0003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0003 : AngleCell :=
  childHH (childLL (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0010 : AngleCell :=
  childLL (childLH (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0011 : AngleCell :=
  childLH (childLH (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0012 : AngleCell :=
  childHL (childLH (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0013 : AngleCell :=
  childHH (childLH (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0100 : AngleCell :=
  childLL (childLL (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0102 : AngleCell :=
  childHL (childLL (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0103 : AngleCell :=
  childHH (childLL (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0112 : AngleCell :=
  childHL (childLH (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0113 : AngleCell :=
  childHH (childLH (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `1002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1002 : AngleCell :=
  childHL (childLL (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1121 : AngleCell :=
  childLH (childHL (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1130 : AngleCell :=
  childLL (childHH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1131 : AngleCell :=
  childLH (childHH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11012132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaBelowCell1101)))

/-- Subcell `11012133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaBelowCell1101)))

/-- Subcell `11013013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaBelowCell1101)))

/-- Subcell `11013021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaBelowCell1101)))

/-- Subcell `11013022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell1101)))

/-- Subcell `11013023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell1101)))

/-- Subcell `11013030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaBelowCell1101)))

/-- Subcell `11013031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaBelowCell1101)))

/-- Subcell `11013032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell1101)))

/-- Subcell `11013033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell1101)))

/-- Subcell `11013102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaBelowCell1101)))

/-- Subcell `11013103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaBelowCell1101)))

/-- Subcell `11013112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell1101)))

/-- Subcell `11013113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell1101)))

/-- Subcell `11013120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaBelowCell1101)))

/-- Subcell `11013121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaBelowCell1101)))

/-- Subcell `11013122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell1101)))

/-- Subcell `11013123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell1101)))

/-- Subcell `11013130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell1101)))

/-- Subcell `11013131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell1101)))

/-- Subcell `11013132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell1101)))

/-- Subcell `11013133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell1101)))

/-- Subcell `11102002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaBelowCell1110)))

/-- Subcell `11102003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaBelowCell1110)))

/-- Subcell `11102012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaBelowCell1110)))

/-- Subcell `11102013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaBelowCell1110)))

/-- Subcell `11102020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaBelowCell1110)))

/-- Subcell `11102021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaBelowCell1110)))

/-- Subcell `11102022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaBelowCell1110)))

/-- Subcell `11102023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaBelowCell1110)))

/-- Subcell `11102030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaBelowCell1110)))

/-- Subcell `11102031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaBelowCell1110)))

/-- Subcell `11102032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaBelowCell1110)))

/-- Subcell `11102033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaBelowCell1110)))

/-- Subcell `11102120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaBelowCell1110)))

/-- Subcell `11102121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaBelowCell1110)))

/-- Subcell `11102122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaBelowCell1110)))

/-- Subcell `11102123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaBelowCell1110)))

/-- Subcell `11102130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaBelowCell1110)))

/-- Subcell `11102131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaBelowCell1110)))

/-- Subcell `11102132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaBelowCell1110)))

/-- Subcell `11102133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaBelowCell1110)))

/-- Subcell `11102200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaBelowCell1110)))

/-- Subcell `11102201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaBelowCell1110)))

/-- Subcell `11102210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaBelowCell1110)))

/-- Subcell `11102211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaBelowCell1110)))

/-- Subcell `11102300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaBelowCell1110)))

/-- Subcell `11102301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaBelowCell1110)))

/-- Subcell `11102310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaBelowCell1110)))

/-- Subcell `11102311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaBelowCell1110)))

/-- Subcell `11103020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaBelowCell1110)))

/-- Subcell `11103201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaBelowCell1110)))

/-- Subcell `11103210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaBelowCell1110)))

/-- Subcell `11103211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaBelowCell1110)))

/-- Subcell `11103300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11103301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11103310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11103311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11112020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11113022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaBelowCell1111)))

end GerverSofa.PartE.CertificateCells6754c8bb3e

namespace GerverSofa.PartE.CertificateCellse9ea903ef1

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCellse9ea903ef1

namespace GerverSofa.PartE.CertificateCells89d797401e

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCells89d797401e

namespace GerverSofa.PartE.CertificateCellsafdf6e4305

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCellsafdf6e4305

namespace GerverSofa.PartE.CertificateCells0d2c374949

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCells0d2c374949

namespace GerverSofa.PartE.CertificateCells3df86e4955

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCells3df86e4955

namespace GerverSofa.PartE.CertificateCells3298a326ef

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCells3298a326ef

namespace GerverSofa.PartE.CertificateCells47980ca575

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCells47980ca575

namespace GerverSofa.PartE.CertificateCellsfed39385df

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCellsfed39385df

namespace GerverSofa.PartE.CertificateCellsb1b33fecca

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCellsb1b33fecca

namespace GerverSofa.PartE.CertificateCellsc427a8578f

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCellsc427a8578f

namespace GerverSofa.PartE.CertificateCells25978ec18d

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCells25978ec18d

namespace GerverSofa.PartE.CertificateCellse6161a42be

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011011` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011011 : AngleCell :=
  childLH (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCellse6161a42be

namespace GerverSofa.PartE.CertificateCells1f6ffcc997

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011011` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011011 : AngleCell :=
  childLH (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCells1f6ffcc997

namespace GerverSofa.PartE.CertificateCells1275d3adc4

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011011` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011011 : AngleCell :=
  childLH (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCells1275d3adc4

namespace GerverSofa.PartE.CertificateCells021b870816

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011011` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011011 : AngleCell :=
  childLH (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCells021b870816

namespace GerverSofa.PartE.CertificateCells9ade3f586f

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011011` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011011 : AngleCell :=
  childLH (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCells9ade3f586f

namespace GerverSofa.PartE.CertificateCellsfd8221930a

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011011` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011011 : AngleCell :=
  childLH (childLH (childLL (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCellsfd8221930a

namespace GerverSofa.PartE.CertificateCells5aaf24f73d

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

end GerverSofa.PartE.CertificateCells5aaf24f73d

namespace GerverSofa.PartE.CertificateCells31cca9f2c5

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011100` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011100 : AngleCell :=
  childLL (childLL (childLH (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCells31cca9f2c5

namespace GerverSofa.PartE.CertificateCells0a8495a296

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011100` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011100 : AngleCell :=
  childLL (childLL (childLH (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCells0a8495a296

namespace GerverSofa.PartE.CertificateCells4cabb07dbd

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011100` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011100 : AngleCell :=
  childLL (childLL (childLH (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCells4cabb07dbd

namespace GerverSofa.PartE.CertificateCellsc6c93e8f5c

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011100` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011100 : AngleCell :=
  childLL (childLL (childLH (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCellsc6c93e8f5c

namespace GerverSofa.PartE.CertificateCellsaa40da30f6

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011101 : AngleCell :=
  childLH (childLL (childLH (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCellsaa40da30f6

namespace GerverSofa.PartE.CertificateCells919c5d7ca9

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

end GerverSofa.PartE.CertificateCells919c5d7ca9

namespace GerverSofa.PartE.CertificateCells87d4f5e678

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011110 : AngleCell :=
  childLL (childLH (childLH (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCells87d4f5e678

namespace GerverSofa.PartE.CertificateCellsefc5f924ee

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011110 : AngleCell :=
  childLL (childLH (childLH (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCellsefc5f924ee

namespace GerverSofa.PartE.CertificateCellsac583a159d

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11011111` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011111 : AngleCell :=
  childLH (childLH (childLH (childLH phiAboveCell1101)))

end GerverSofa.PartE.CertificateCellsac583a159d

namespace GerverSofa.PartE.CertificateCellsf317a94cb3

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

end GerverSofa.PartE.CertificateCellsf317a94cb3

namespace GerverSofa.PartE.CertificateCellsf7dce840c8

/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `11100000` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100000 : AngleCell :=
  childLL (childLL (childLL (childLL phiAboveCell1110)))

end GerverSofa.PartE.CertificateCellsf7dce840c8

namespace GerverSofa.PartE.CertificateCells5fe660c4fc

/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))

end GerverSofa.PartE.CertificateCells5fe660c4fc

namespace GerverSofa.PartE.CertificateCells7e3a6c7b6b

/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))

end GerverSofa.PartE.CertificateCells7e3a6c7b6b

namespace GerverSofa.PartE.CertificateCellsa5efdb03f3

/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))

end GerverSofa.PartE.CertificateCellsa5efdb03f3

namespace GerverSofa.PartE.CertificateCells4f05b2093e

/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))

end GerverSofa.PartE.CertificateCells4f05b2093e

namespace GerverSofa.PartE.CertificateCellsa15368d7db

/-- Subcell `1001` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1001 : AngleCell :=
  childLH (childLL (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1010 : AngleCell :=
  childLL (childLH (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1011` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1011 : AngleCell :=
  childLH (childLH (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1100` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1100 : AngleCell :=
  childLL (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1111` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `0101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0101 : AngleCell :=
  childLH (childLL (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0110 : AngleCell :=
  childLL (childLH (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0111` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0111 : AngleCell :=
  childLH (childLH (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `1000` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1000 : AngleCell :=
  childLL (childLL (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `0000` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0001` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0001 : AngleCell :=
  childLH (childLL (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0010 : AngleCell :=
  childLL (childLH (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0011` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0011 : AngleCell :=
  childLH (childLH (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0100` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0100 : AngleCell :=
  childLL (childLL (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `1002` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1002 : AngleCell :=
  childHL (childLL (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1003` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1003 : AngleCell :=
  childHH (childLL (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1012` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1012 : AngleCell :=
  childHL (childLH (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1013` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1013 : AngleCell :=
  childHH (childLH (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1102` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1102 : AngleCell :=
  childHL (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1103` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1103 : AngleCell :=
  childHH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1112` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1112 : AngleCell :=
  childHL (childLH (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1113` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1113 : AngleCell :=
  childHH (childLH (childLH (childLH e24PhiAboveRoot)))

end GerverSofa.PartE.CertificateCellsa15368d7db

namespace GerverSofa.PartE.CertificateCells12ecbb1984

/-- Subcell `3320` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3320 : AngleCell :=
  childLL (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCells12ecbb1984

namespace GerverSofa.PartE.CertificateCellsf9b1d22c2c

/-- Subcell `3322` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3322 : AngleCell :=
  childHL (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCellsf9b1d22c2c

namespace GerverSofa.PartE.CertificateCells5481d87062

/-- Subcell `3322` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3322 : AngleCell :=
  childHL (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCells5481d87062

namespace GerverSofa.PartE.CertificateCellsc99c114252

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCellsc99c114252

namespace GerverSofa.PartE.CertificateCells85102f4bff

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCells85102f4bff

namespace GerverSofa.PartE.CertificateCellsd7423e4c3b

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCellsd7423e4c3b

namespace GerverSofa.PartE.CertificateCells8ae9088aab

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCells8ae9088aab

namespace GerverSofa.PartE.CertificateCellsb8a79b56b3

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCellsb8a79b56b3

namespace GerverSofa.PartE.CertificateCells13ae325d6d

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCells13ae325d6d

namespace GerverSofa.PartE.CertificateCells6add7bae04

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCells6add7bae04

namespace GerverSofa.PartE.CertificateCellscd1d17c9b4

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCellscd1d17c9b4

namespace GerverSofa.PartE.CertificateCells709ea69226

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33232311` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33232311 : AngleCell :=
  childLH (childLH (childHH (childHL phiBelowCell3323)))

end GerverSofa.PartE.CertificateCells709ea69226

namespace GerverSofa.PartE.CertificateCellsade8569b0a

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33232313` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33232313 : AngleCell :=
  childHH (childLH (childHH (childHL phiBelowCell3323)))

end GerverSofa.PartE.CertificateCellsade8569b0a

namespace GerverSofa.PartE.CertificateCellsfece773e85

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCellsfece773e85

namespace GerverSofa.PartE.CertificateCellse593ec4a84

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33232331` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33232331 : AngleCell :=
  childLH (childHH (childHH (childHL phiBelowCell3323)))

end GerverSofa.PartE.CertificateCellse593ec4a84

namespace GerverSofa.PartE.CertificateCells0ccc164bd1

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCells0ccc164bd1

namespace GerverSofa.PartE.CertificateCells072df6b25f

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCells072df6b25f

namespace GerverSofa.PartE.CertificateCells215f6c9ebd

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCells215f6c9ebd

namespace GerverSofa.PartE.CertificateCellsef857ed1c7

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCellsef857ed1c7

namespace GerverSofa.PartE.CertificateCells2ebe0c2db9

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233202` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233202 : AngleCell :=
  childHL (childLL (childHL (childHH phiBelowCell3323)))

end GerverSofa.PartE.CertificateCells2ebe0c2db9

namespace GerverSofa.PartE.CertificateCells27c0e8c594

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCells27c0e8c594

namespace GerverSofa.PartE.CertificateCells4d117fb26d

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233220` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233220 : AngleCell :=
  childLL (childHL (childHL (childHH phiBelowCell3323)))

end GerverSofa.PartE.CertificateCells4d117fb26d

namespace GerverSofa.PartE.CertificateCells848f180c5a

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233220` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233220 : AngleCell :=
  childLL (childHL (childHL (childHH phiBelowCell3323)))

end GerverSofa.PartE.CertificateCells848f180c5a

namespace GerverSofa.PartE.CertificateCells090e12bc76

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233221` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233221 : AngleCell :=
  childLH (childHL (childHL (childHH phiBelowCell3323)))

end GerverSofa.PartE.CertificateCells090e12bc76

namespace GerverSofa.PartE.CertificateCells857be56025

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233222` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233222 : AngleCell :=
  childHL (childHL (childHL (childHH phiBelowCell3323)))

end GerverSofa.PartE.CertificateCells857be56025

namespace GerverSofa.PartE.CertificateCellsea76f7562d

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233222` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233222 : AngleCell :=
  childHL (childHL (childHL (childHH phiBelowCell3323)))

end GerverSofa.PartE.CertificateCellsea76f7562d

namespace GerverSofa.PartE.CertificateCellsdd77c2320b

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233223 : AngleCell :=
  childHH (childHL (childHL (childHH phiBelowCell3323)))

end GerverSofa.PartE.CertificateCellsdd77c2320b

namespace GerverSofa.PartE.CertificateCells08c6706994

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233223 : AngleCell :=
  childHH (childHL (childHL (childHH phiBelowCell3323)))

/-- Subcell `332332232120` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell332332232120 : AngleCell :=
  childLL (childHL (childLH (childHL phiBelowCell33233223)))

end GerverSofa.PartE.CertificateCells08c6706994

namespace GerverSofa.PartE.CertificateCells96d537e773

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233223 : AngleCell :=
  childHH (childHL (childHL (childHH phiBelowCell3323)))

end GerverSofa.PartE.CertificateCells96d537e773

namespace GerverSofa.PartE.CertificateCells0abe1d75a7

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233223 : AngleCell :=
  childHH (childHL (childHL (childHH phiBelowCell3323)))

end GerverSofa.PartE.CertificateCells0abe1d75a7

namespace GerverSofa.PartE.CertificateCells4849d1c13b

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233223 : AngleCell :=
  childHH (childHL (childHL (childHH phiBelowCell3323)))

end GerverSofa.PartE.CertificateCells4849d1c13b

namespace GerverSofa.PartE.CertificateCellsf2740dc787

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233223 : AngleCell :=
  childHH (childHL (childHL (childHH phiBelowCell3323)))

end GerverSofa.PartE.CertificateCellsf2740dc787

namespace GerverSofa.PartE.CertificateCells3f18540de9

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233223 : AngleCell :=
  childHH (childHL (childHL (childHH phiBelowCell3323)))

end GerverSofa.PartE.CertificateCells3f18540de9

namespace GerverSofa.PartE.CertificateCellsa21caf16f2

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233223 : AngleCell :=
  childHH (childHL (childHL (childHH phiBelowCell3323)))

end GerverSofa.PartE.CertificateCellsa21caf16f2

namespace GerverSofa.PartE.CertificateCells21943a9b83

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233223 : AngleCell :=
  childHH (childHL (childHL (childHH phiBelowCell3323)))

end GerverSofa.PartE.CertificateCells21943a9b83

namespace GerverSofa.PartE.CertificateCells62ff50a4e8

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCells62ff50a4e8

namespace GerverSofa.PartE.CertificateCells6677fc4b7c

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `33233232` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233232 : AngleCell :=
  childHL (childHH (childHL (childHH phiBelowCell3323)))

end GerverSofa.PartE.CertificateCells6677fc4b7c

namespace GerverSofa.PartE.CertificateCells07875eeb47

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCells07875eeb47

namespace GerverSofa.PartE.CertificateCells5ed2775b48

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCells5ed2775b48

namespace GerverSofa.PartE.CertificateCells83d9ff7319

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCells83d9ff7319

namespace GerverSofa.PartE.CertificateCells240a9bf558

/-- Subcell `3000` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3000 : AngleCell :=
  childLL (childLL (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3001` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3001 : AngleCell :=
  childLH (childLL (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3002` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3002 : AngleCell :=
  childHL (childLL (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3003` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3003 : AngleCell :=
  childHH (childLL (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3010` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3010 : AngleCell :=
  childLL (childLH (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3011` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3011 : AngleCell :=
  childLH (childLH (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3012` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3012 : AngleCell :=
  childHL (childLH (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3013` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3013 : AngleCell :=
  childHH (childLH (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3020` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3020 : AngleCell :=
  childLL (childHL (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3021` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3021 : AngleCell :=
  childLH (childHL (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3022` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3022 : AngleCell :=
  childHL (childHL (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3023` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3023 : AngleCell :=
  childHH (childHL (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3030` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3030 : AngleCell :=
  childLL (childHH (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3031` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3031 : AngleCell :=
  childLH (childHH (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3032` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3032 : AngleCell :=
  childHL (childHH (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3033` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3033 : AngleCell :=
  childHH (childHH (childLL (childHH e24PhiBelowRoot)))

/-- Subcell `3100` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3100 : AngleCell :=
  childLL (childLL (childLH (childHH e24PhiBelowRoot)))

/-- Subcell `3101` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3101 : AngleCell :=
  childLH (childLL (childLH (childHH e24PhiBelowRoot)))

/-- Subcell `3102` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3102 : AngleCell :=
  childHL (childLL (childLH (childHH e24PhiBelowRoot)))

/-- Subcell `3103` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3103 : AngleCell :=
  childHH (childLL (childLH (childHH e24PhiBelowRoot)))

/-- Subcell `3112` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3112 : AngleCell :=
  childHL (childLH (childLH (childHH e24PhiBelowRoot)))

/-- Subcell `3120` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3120 : AngleCell :=
  childLL (childHL (childLH (childHH e24PhiBelowRoot)))

/-- Subcell `3121` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3121 : AngleCell :=
  childLH (childHL (childLH (childHH e24PhiBelowRoot)))

/-- Subcell `3122` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3122 : AngleCell :=
  childHL (childHL (childLH (childHH e24PhiBelowRoot)))

/-- Subcell `3123` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3123 : AngleCell :=
  childHH (childHL (childLH (childHH e24PhiBelowRoot)))

/-- Subcell `3130` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3130 : AngleCell :=
  childLL (childHH (childLH (childHH e24PhiBelowRoot)))

/-- Subcell `3131` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3131 : AngleCell :=
  childLH (childHH (childLH (childHH e24PhiBelowRoot)))

/-- Subcell `3132` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3132 : AngleCell :=
  childHL (childHH (childLH (childHH e24PhiBelowRoot)))

/-- Subcell `3133` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3133 : AngleCell :=
  childHH (childHH (childLH (childHH e24PhiBelowRoot)))

/-- Subcell `3200` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3200 : AngleCell :=
  childLL (childLL (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3201` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3201 : AngleCell :=
  childLH (childLL (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3202` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3202 : AngleCell :=
  childHL (childLL (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3203` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3203 : AngleCell :=
  childHH (childLL (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3210` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3210 : AngleCell :=
  childLL (childLH (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3211` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3211 : AngleCell :=
  childLH (childLH (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3212` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3212 : AngleCell :=
  childHL (childLH (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3213` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3213 : AngleCell :=
  childHH (childLH (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3220` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3220 : AngleCell :=
  childLL (childHL (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3221` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3221 : AngleCell :=
  childLH (childHL (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3222` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3222 : AngleCell :=
  childHL (childHL (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3223 : AngleCell :=
  childHH (childHL (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3230` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3230 : AngleCell :=
  childLL (childHH (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3231` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3231 : AngleCell :=
  childLH (childHH (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3232` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3232 : AngleCell :=
  childHL (childHH (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3233` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3233 : AngleCell :=
  childHH (childHH (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3300` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3300 : AngleCell :=
  childLL (childLL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3301` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3301 : AngleCell :=
  childLH (childLL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3302` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3302 : AngleCell :=
  childHL (childLL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3303` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3303 : AngleCell :=
  childHH (childLL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3310` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3310 : AngleCell :=
  childLL (childLH (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3311` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3311 : AngleCell :=
  childLH (childLH (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3312` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3312 : AngleCell :=
  childHL (childLH (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3313` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3313 : AngleCell :=
  childHH (childLH (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3320` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3320 : AngleCell :=
  childLL (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3321` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3321 : AngleCell :=
  childLH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3322` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3322 : AngleCell :=
  childHL (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3330` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3330 : AngleCell :=
  childLL (childHH (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3331` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3331 : AngleCell :=
  childLH (childHH (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3332` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3332 : AngleCell :=
  childHL (childHH (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3333` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3333 : AngleCell :=
  childHH (childHH (childHH (childHH e24PhiBelowRoot)))

end GerverSofa.PartE.CertificateCells240a9bf558

namespace GerverSofa.PartE.CertificateCells22695df69a

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells22695df69a

namespace GerverSofa.PartE.CertificateCells782ac45202

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells782ac45202

namespace GerverSofa.PartE.CertificateCellsb8f48433cf

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsb8f48433cf

namespace GerverSofa.PartE.CertificateCells5bc1aa1a31

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells5bc1aa1a31

namespace GerverSofa.PartE.CertificateCells29b43c6eb7

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells29b43c6eb7

namespace GerverSofa.PartE.CertificateCells64bf70ad53

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells64bf70ad53

namespace GerverSofa.PartE.CertificateCellsc935d550f9

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsc935d550f9

namespace GerverSofa.PartE.CertificateCells0a80d69c2b

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells0a80d69c2b

namespace GerverSofa.PartE.CertificateCellsfd35b16333

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsfd35b16333

namespace GerverSofa.PartE.CertificateCellsd8bbac8cc5

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsd8bbac8cc5

namespace GerverSofa.PartE.CertificateCells2eb3bc7e90

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells2eb3bc7e90

namespace GerverSofa.PartE.CertificateCellsbc99de789e

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsbc99de789e

namespace GerverSofa.PartE.CertificateCellsdc52d78b64

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsdc52d78b64

namespace GerverSofa.PartE.CertificateCells69f98d6dd4

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells69f98d6dd4

namespace GerverSofa.PartE.CertificateCells675835e7b9

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells675835e7b9

namespace GerverSofa.PartE.CertificateCellsda5cde5aa9

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsda5cde5aa9

namespace GerverSofa.PartE.CertificateCellsed33eab041

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsed33eab041

namespace GerverSofa.PartE.CertificateCellsf997ca54bf

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsf997ca54bf

namespace GerverSofa.PartE.CertificateCellsba35077fe5

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsba35077fe5

namespace GerverSofa.PartE.CertificateCells5d0bfdcc89

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells5d0bfdcc89

namespace GerverSofa.PartE.CertificateCellsb9eba9ae01

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsb9eba9ae01

namespace GerverSofa.PartE.CertificateCells5ae8bbaf2e

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells5ae8bbaf2e

namespace GerverSofa.PartE.CertificateCellsbec28e0304

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsbec28e0304

namespace GerverSofa.PartE.CertificateCells1b578c3d10

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells1b578c3d10

namespace GerverSofa.PartE.CertificateCells2bc65b7190

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells2bc65b7190

namespace GerverSofa.PartE.CertificateCellsc46dbfc77b

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsc46dbfc77b

namespace GerverSofa.PartE.CertificateCells752b604750

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells752b604750

namespace GerverSofa.PartE.CertificateCellse66f3ce3f5

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellse66f3ce3f5

namespace GerverSofa.PartE.CertificateCells45a373af38

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

end GerverSofa.PartE.CertificateCells45a373af38

namespace GerverSofa.PartE.CertificateCellsdabf824b24

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsdabf824b24

namespace GerverSofa.PartE.CertificateCells11c2c46ea8

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells11c2c46ea8

namespace GerverSofa.PartE.CertificateCellsfc2738963a

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsfc2738963a

namespace GerverSofa.PartE.CertificateCells2c3b2a68a2

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells2c3b2a68a2

namespace GerverSofa.PartE.CertificateCells024fe9d391

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells024fe9d391

namespace GerverSofa.PartE.CertificateCells95bf7ab700

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells95bf7ab700

namespace GerverSofa.PartE.CertificateCellsb2f77f238f

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsb2f77f238f

namespace GerverSofa.PartE.CertificateCells8179cb7dd8

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells8179cb7dd8

namespace GerverSofa.PartE.CertificateCellsdb257f0c7c

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsdb257f0c7c

namespace GerverSofa.PartE.CertificateCells3a304b7358

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells3a304b7358

namespace GerverSofa.PartE.CertificateCells6cdc8e3bc2

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells6cdc8e3bc2

namespace GerverSofa.PartE.CertificateCells0157659d62

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells0157659d62

namespace GerverSofa.PartE.CertificateCells834e9932ec

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells834e9932ec

namespace GerverSofa.PartE.CertificateCellsb02c7d0e39

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `000022002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `000022002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `000022002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `000022002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `000022002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `000022002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `000022002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsb02c7d0e39

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Combining adaptive-cover certificates

The numerical leaf checks are imported separately so that they can compile in parallel.
This module combines them using the adaptive-cover soundness lemmas.

* `KernelOnly.PartE.E24KC6ThetaBelowReconstruct`.
* `KernelOnly.PartE.PhiAbove.Join00029`.
* `KernelOnly.PartE.PhiAbove.Join00036`.
* `KernelOnly.PartE.PhiAbove.Join00042`.
* `KernelOnly.PartE.PhiAbove.Join00045`.
* `KernelOnly.PartE.PhiAbove.Join00048`.
* `KernelOnly.PartE.PhiAbove.Join00056`.
* `KernelOnly.PartE.PhiAbove.Join00062`.
* `KernelOnly.PartE.PhiAbove.Join00065`.
* `KernelOnly.PartE.PhiAbove.Join00071`.
* `KernelOnly.PartE.PhiAbove.Join00074`.
* `KernelOnly.PartE.PhiAbove.Join00077`.
* `KernelOnly.PartE.PhiAbove.Join00085`.
* `KernelOnly.PartE.PhiAbove.Join00091`.
* `KernelOnly.PartE.PhiAbove.Join00094`.
* `KernelOnly.PartE.PhiAbove.Join00101`.
* `KernelOnly.PartE.PhiAbove.Join00105`.
* `KernelOnly.PartE.PhiAbove.Join00108`.
* `KernelOnly.PartE.PhiAbove.Join00111`.
* `KernelOnly.PartE.PhiAbove.Join00122`.
* `KernelOnly.PartE.PhiAbove.Join00129`.
* `KernelOnly.PartE.PhiAbove.Join00133`.
* `KernelOnly.PartE.PhiAbove.Join00136`.
* `KernelOnly.PartE.PhiAbove.Join00142`.
* `KernelOnly.PartE.PhiAbove.Join00145`.
* `KernelOnly.PartE.PhiAbove.Join00156`.
* `KernelOnly.PartE.PhiAbove.Join00159`.
* `KernelOnly.PartE.PhiAbove.Join00165`.
* `KernelOnly.PartE.PhiAbove.Join00168`.
* `KernelOnly.PartE.PhiAbove.Join00178`.
* `KernelOnly.PartE.PhiAbove.Join00182`.
* `KernelOnly.PartE.PhiAbove.Join00191`.
* `KernelOnly.PartE.PhiAbove.Join00200`.
* `KernelOnly.PartE.PhiAbove.Join00208`.
* `KernelOnly.PartE.E24KC6PhiAboveReconstruct`.
* `KernelOnly.PartE.PhiBelow.Join00246`.
* `KernelOnly.PartE.PhiBelow.Join00260`.
* `KernelOnly.PartE.PhiBelow.Join00269`.
* `KernelOnly.PartE.PhiBelow.Join00278`.
* `KernelOnly.PartE.PhiBelow.Join00284`.
* `KernelOnly.PartE.PhiBelow.Join00285`.
* `KernelOnly.PartE.PhiBelow.Join00294`.
* `KernelOnly.PartE.PhiBelow.Join00301`.
* `KernelOnly.PartE.PhiBelow.Join00308`.
* `KernelOnly.PartE.PhiBelow.Join00314`.
* `KernelOnly.PartE.PhiBelow.Join00315`.
* `KernelOnly.PartE.PhiBelow.Join00326`.
* `KernelOnly.PartE.PhiBelow.Join00333`.
* `KernelOnly.PartE.PhiBelow.Join00334`.
* `KernelOnly.PartE.PhiBelow.Join00343`.
* `KernelOnly.PartE.PhiBelow.Join00346`.
* `KernelOnly.PartE.PhiBelow.Join00347`.
* `KernelOnly.PartE.PhiBelow.Join00348`.
* `KernelOnly.PartE.PhiBelow.Join00358`.
* `KernelOnly.PartE.PhiBelow.Join00369`.
* `KernelOnly.PartE.PhiBelow.Join00371`.
* `KernelOnly.PartE.PhiBelow.Join00383`.
* `KernelOnly.PartE.PhiBelow.Join00384`.
* `KernelOnly.PartE.PhiBelow.Join00390`.
* `KernelOnly.PartE.PhiBelow.Join00398`.
* `KernelOnly.PartE.PhiBelow.Join00401`.
* `KernelOnly.PartE.PhiBelow.Join00408`.
* `KernelOnly.PartE.PhiBelow.Join00421`.
* `KernelOnly.PartE.PhiBelow.Join00425`.
* `KernelOnly.PartE.PhiBelow.Join00427`.
* `KernelOnly.PartE.PhiBelow.Join00434`.
* `KernelOnly.PartE.PhiBelow.Join00435`.
* `KernelOnly.PartE.PhiBelow.Join00444`.
* `KernelOnly.PartE.PhiBelow.Join00446`.
* `KernelOnly.PartE.PhiBelow.Join00447`.
* `KernelOnly.PartE.PhiBelow.Join00448`.
* `KernelOnly.PartE.PhiBelow.Join00457`.
* `KernelOnly.PartE.PhiBelow.Join00459`.
* `KernelOnly.PartE.PhiBelow.Join00460`.
* `KernelOnly.PartE.PhiBelow.Join00462`.
* `KernelOnly.PartE.E24KC6PhiBelowReconstruct`.
* `KernelOnly.PartE.ThetaAbove.Join00016`.
* `KernelOnly.PartE.ThetaAbove.Join00022`.
* `KernelOnly.PartE.ThetaAbove.Join00023`.
* `KernelOnly.PartE.ThetaAbove.Join00484`.
* `KernelOnly.PartE.ThetaAbove.Join00490`.
* `KernelOnly.PartE.ThetaAbove.Join00493`.
* `KernelOnly.PartE.ThetaAbove.Join00500`.
* `KernelOnly.PartE.ThetaAbove.Join00506`.
* `KernelOnly.PartE.ThetaAbove.Join00509`.
* `KernelOnly.PartE.ThetaAbove.Join00512`.
* `KernelOnly.PartE.ThetaAbove.Join00520`.
* `KernelOnly.PartE.ThetaAbove.Join00526`.
* `KernelOnly.PartE.ThetaAbove.Join00529`.
* `KernelOnly.PartE.ThetaAbove.Join00536`.
* `KernelOnly.PartE.ThetaAbove.Join00542`.
* `KernelOnly.PartE.ThetaAbove.Join00545`.
* `KernelOnly.PartE.ThetaAbove.Join00548`.
* `KernelOnly.PartE.ThetaAbove.Join00549`.
* `KernelOnly.PartE.ThetaAbove.Join00560`.
* `KernelOnly.PartE.ThetaAbove.Join00566`.
* `KernelOnly.PartE.ThetaAbove.Join00569`.
* `KernelOnly.PartE.ThetaAbove.Join00576`.
* `KernelOnly.PartE.ThetaAbove.Join00580`.
* `KernelOnly.PartE.ThetaAbove.Join00583`.
* `KernelOnly.PartE.ThetaAbove.Join00590`.
* `KernelOnly.PartE.ThetaAbove.Join00596`.
* `KernelOnly.PartE.ThetaAbove.Join00599`.
* `KernelOnly.PartE.ThetaAbove.Join00600`.
* `KernelOnly.PartE.ThetaAbove.Join00603`.
* `KernelOnly.PartE.ThetaAbove.Join00614`.
* `KernelOnly.PartE.ThetaAbove.Join00620`.
* `KernelOnly.PartE.ThetaAbove.Join00623`.
* `KernelOnly.PartE.ThetaAbove.Join00630`.
* `KernelOnly.PartE.ThetaAbove.Join00636`.
* `KernelOnly.PartE.ThetaAbove.Join00639`.
* `KernelOnly.PartE.ThetaAbove.Join00640`.
* `KernelOnly.PartE.ThetaAbove.Join00650`.
* `KernelOnly.PartE.ThetaAbove.Join00656`.
* `KernelOnly.PartE.ThetaAbove.Join00659`.
* `KernelOnly.PartE.ThetaAbove.Join00666`.
* `KernelOnly.PartE.ThetaAbove.Join00026`.
* `KernelOnly.PartE.ThetaAbove.Join00027`.
* `KernelOnly.PartE.E24KC6ProofBatch9b503cfa8ccc3ab1`.
-/

public section

noncomputable section

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC6Theta Below Reconstruct
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6754c8bb3e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells6754c8bb3e

open CertificateCells6754c8bb3e

theorem e24KC2ThetaBelowNode11012132 :
    adaptiveCoverCheck 10 thetaBelowCell11012132 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11012132
    e24KC2ThetaBelowLeaf110121320 e24KC2ThetaBelowLeaf110121321 e24KC2ThetaBelowLeaf110121322
      e24KC2ThetaBelowLeaf110121323

theorem e24KC2ThetaBelowNode11012133 :
    adaptiveCoverCheck 10 thetaBelowCell11012133 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11012133
    e24KC2ThetaBelowLeaf110121330 e24KC2ThetaBelowLeaf110121331 e24KC2ThetaBelowLeaf110121332
      e24KC2ThetaBelowLeaf110121333

theorem e24KC2ThetaBelowNode11013013 :
    adaptiveCoverCheck 10 thetaBelowCell11013013 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013013
    e24KC2ThetaBelowLeaf110130130 e24KC2ThetaBelowLeaf110130131 e24KC2ThetaBelowLeaf110130132
      e24KC2ThetaBelowLeaf110130133

theorem e24KC2ThetaBelowNode11013021 :
    adaptiveCoverCheck 10 thetaBelowCell11013021 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013021
    e24KC2ThetaBelowLeaf110130210 e24KC2ThetaBelowLeaf110130211 e24KC2ThetaBelowLeaf110130212
      e24KC2ThetaBelowLeaf110130213

theorem e24KC2ThetaBelowNode11013022 :
    adaptiveCoverCheck 10 thetaBelowCell11013022 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013022
    e24KC2ThetaBelowLeaf110130220 e24KC2ThetaBelowLeaf110130221 e24KC2ThetaBelowLeaf110130222
      e24KC2ThetaBelowLeaf110130223

theorem e24KC2ThetaBelowNode11013023 :
    adaptiveCoverCheck 10 thetaBelowCell11013023 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013023
    e24KC2ThetaBelowLeaf110130230 e24KC2ThetaBelowLeaf110130231 e24KC2ThetaBelowLeaf110130232
      e24KC2ThetaBelowLeaf110130233

theorem e24KC2ThetaBelowNode11013030 :
    adaptiveCoverCheck 10 thetaBelowCell11013030 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013030
    e24KC2ThetaBelowLeaf110130300 e24KC2ThetaBelowLeaf110130301 e24KC2ThetaBelowLeaf110130302
      e24KC2ThetaBelowLeaf110130303

theorem e24KC2ThetaBelowNode11013031 :
    adaptiveCoverCheck 10 thetaBelowCell11013031 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013031
    e24KC2ThetaBelowLeaf110130310 e24KC2ThetaBelowLeaf110130311 e24KC2ThetaBelowLeaf110130312
      e24KC2ThetaBelowLeaf110130313

theorem e24KC2ThetaBelowNode11013032 :
    adaptiveCoverCheck 10 thetaBelowCell11013032 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013032
    e24KC2ThetaBelowLeaf110130320 e24KC2ThetaBelowLeaf110130321 e24KC2ThetaBelowLeaf110130322
      e24KC2ThetaBelowLeaf110130323

theorem e24KC2ThetaBelowNode11013033 :
    adaptiveCoverCheck 10 thetaBelowCell11013033 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013033
    e24KC2ThetaBelowLeaf110130330 e24KC2ThetaBelowLeaf110130331 e24KC2ThetaBelowLeaf110130332
      e24KC2ThetaBelowLeaf110130333

theorem e24KC2ThetaBelowNode11013102 :
    adaptiveCoverCheck 10 thetaBelowCell11013102 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013102
    e24KC2ThetaBelowLeaf110131020 e24KC2ThetaBelowLeaf110131021 e24KC2ThetaBelowLeaf110131022
      e24KC2ThetaBelowLeaf110131023

theorem e24KC2ThetaBelowNode11013103 :
    adaptiveCoverCheck 10 thetaBelowCell11013103 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013103
    e24KC2ThetaBelowLeaf110131030 e24KC2ThetaBelowLeaf110131031 e24KC2ThetaBelowLeaf110131032
      e24KC2ThetaBelowLeaf110131033

theorem e24KC2ThetaBelowNode11013112 :
    adaptiveCoverCheck 10 thetaBelowCell11013112 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013112
    e24KC2ThetaBelowLeaf110131120 e24KC2ThetaBelowLeaf110131121 e24KC2ThetaBelowLeaf110131122
      e24KC2ThetaBelowLeaf110131123

theorem e24KC2ThetaBelowNode11013113 :
    adaptiveCoverCheck 10 thetaBelowCell11013113 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013113
    e24KC2ThetaBelowLeaf110131130 e24KC2ThetaBelowLeaf110131131 e24KC2ThetaBelowLeaf110131132
      e24KC2ThetaBelowLeaf110131133

theorem e24KC2ThetaBelowNode11013120 :
    adaptiveCoverCheck 10 thetaBelowCell11013120 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013120
    e24KC2ThetaBelowLeaf110131200 e24KC2ThetaBelowLeaf110131201 e24KC2ThetaBelowLeaf110131202
      e24KC2ThetaBelowLeaf110131203

theorem e24KC2ThetaBelowNode11013121 :
    adaptiveCoverCheck 10 thetaBelowCell11013121 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013121
    e24KC2ThetaBelowLeaf110131210 e24KC2ThetaBelowLeaf110131211 e24KC2ThetaBelowLeaf110131212
      e24KC2ThetaBelowLeaf110131213

theorem e24KC2ThetaBelowNode11013122 :
    adaptiveCoverCheck 10 thetaBelowCell11013122 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013122
    e24KC2ThetaBelowLeaf110131220 e24KC2ThetaBelowLeaf110131221 e24KC2ThetaBelowLeaf110131222
      e24KC2ThetaBelowLeaf110131223

theorem e24KC2ThetaBelowNode11013123 :
    adaptiveCoverCheck 10 thetaBelowCell11013123 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013123
    e24KC2ThetaBelowLeaf110131230 e24KC2ThetaBelowLeaf110131231 e24KC2ThetaBelowLeaf110131232
      e24KC2ThetaBelowLeaf110131233

theorem e24KC2ThetaBelowNode11013130 :
    adaptiveCoverCheck 10 thetaBelowCell11013130 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013130
    e24KC2ThetaBelowLeaf110131300 e24KC2ThetaBelowLeaf110131301 e24KC2ThetaBelowLeaf110131302
      e24KC2ThetaBelowLeaf110131303

theorem e24KC2ThetaBelowNode11013131 :
    adaptiveCoverCheck 10 thetaBelowCell11013131 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013131
    e24KC2ThetaBelowLeaf110131310 e24KC2ThetaBelowLeaf110131311 e24KC2ThetaBelowLeaf110131312
      e24KC2ThetaBelowLeaf110131313

theorem e24KC2ThetaBelowNode11013132 :
    adaptiveCoverCheck 10 thetaBelowCell11013132 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013132
    e24KC2ThetaBelowLeaf110131320 e24KC2ThetaBelowLeaf110131321 e24KC2ThetaBelowLeaf110131322
      e24KC2ThetaBelowLeaf110131323

theorem e24KC2ThetaBelowNode11013133 :
    adaptiveCoverCheck 10 thetaBelowCell11013133 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013133
    e24KC2ThetaBelowLeaf110131330 e24KC2ThetaBelowLeaf110131331 e24KC2ThetaBelowLeaf110131332
      e24KC2ThetaBelowLeaf110131333

theorem e24KC2ThetaBelowNode11102002 :
    adaptiveCoverCheck 10 thetaBelowCell11102002 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102002
    e24KC2ThetaBelowLeaf111020020 e24KC2ThetaBelowLeaf111020021 e24KC2ThetaBelowLeaf111020022
      e24KC2ThetaBelowLeaf111020023

theorem e24KC2ThetaBelowNode11102003 :
    adaptiveCoverCheck 10 thetaBelowCell11102003 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102003
    e24KC2ThetaBelowLeaf111020030 e24KC2ThetaBelowLeaf111020031 e24KC2ThetaBelowLeaf111020032
      e24KC2ThetaBelowLeaf111020033

theorem e24KC2ThetaBelowNode11102012 :
    adaptiveCoverCheck 10 thetaBelowCell11102012 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102012
    e24KC2ThetaBelowLeaf111020120 e24KC2ThetaBelowLeaf111020121 e24KC2ThetaBelowLeaf111020122
      e24KC2ThetaBelowLeaf111020123

theorem e24KC2ThetaBelowNode11102013 :
    adaptiveCoverCheck 10 thetaBelowCell11102013 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102013
    e24KC2ThetaBelowLeaf111020130 e24KC2ThetaBelowLeaf111020131 e24KC2ThetaBelowLeaf111020132
      e24KC2ThetaBelowLeaf111020133

theorem e24KC2ThetaBelowNode11102020 :
    adaptiveCoverCheck 10 thetaBelowCell11102020 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102020
    e24KC2ThetaBelowLeaf111020200 e24KC2ThetaBelowLeaf111020201 e24KC2ThetaBelowLeaf111020202
      e24KC2ThetaBelowLeaf111020203

theorem e24KC2ThetaBelowNode11102021 :
    adaptiveCoverCheck 10 thetaBelowCell11102021 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102021
    e24KC2ThetaBelowLeaf111020210 e24KC2ThetaBelowLeaf111020211 e24KC2ThetaBelowLeaf111020212
      e24KC2ThetaBelowLeaf111020213

theorem e24KC2ThetaBelowNode11102022 :
    adaptiveCoverCheck 10 thetaBelowCell11102022 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102022
    e24KC2ThetaBelowLeaf111020220 e24KC2ThetaBelowLeaf111020221 e24KC2ThetaBelowLeaf111020222
      e24KC2ThetaBelowLeaf111020223

theorem e24KC2ThetaBelowNode11102023 :
    adaptiveCoverCheck 10 thetaBelowCell11102023 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102023
    e24KC2ThetaBelowLeaf111020230 e24KC2ThetaBelowLeaf111020231 e24KC2ThetaBelowLeaf111020232
      e24KC2ThetaBelowLeaf111020233

theorem e24KC2ThetaBelowNode11102030 :
    adaptiveCoverCheck 10 thetaBelowCell11102030 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102030
    e24KC2ThetaBelowLeaf111020300 e24KC2ThetaBelowLeaf111020301 e24KC2ThetaBelowLeaf111020302
      e24KC2ThetaBelowLeaf111020303

theorem e24KC2ThetaBelowNode11102031 :
    adaptiveCoverCheck 10 thetaBelowCell11102031 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102031
    e24KC2ThetaBelowLeaf111020310 e24KC2ThetaBelowLeaf111020311 e24KC2ThetaBelowLeaf111020312
      e24KC2ThetaBelowLeaf111020313

theorem e24KC2ThetaBelowNode11102032 :
    adaptiveCoverCheck 10 thetaBelowCell11102032 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102032
    e24KC2ThetaBelowLeaf111020320 e24KC2ThetaBelowLeaf111020321 e24KC2ThetaBelowLeaf111020322
      e24KC2ThetaBelowLeaf111020323

theorem e24KC2ThetaBelowNode11102033 :
    adaptiveCoverCheck 10 thetaBelowCell11102033 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102033
    e24KC2ThetaBelowLeaf111020330 e24KC2ThetaBelowLeaf111020331 e24KC2ThetaBelowLeaf111020332
      e24KC2ThetaBelowLeaf111020333

theorem e24KC2ThetaBelowNode11102120 :
    adaptiveCoverCheck 10 thetaBelowCell11102120 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102120
    e24KC2ThetaBelowLeaf111021200 e24KC2ThetaBelowLeaf111021201 e24KC2ThetaBelowLeaf111021202
      e24KC2ThetaBelowLeaf111021203

theorem e24KC2ThetaBelowNode11102121 :
    adaptiveCoverCheck 10 thetaBelowCell11102121 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102121
    e24KC2ThetaBelowLeaf111021210 e24KC2ThetaBelowLeaf111021211 e24KC2ThetaBelowLeaf111021212
      e24KC2ThetaBelowLeaf111021213

theorem e24KC2ThetaBelowNode11102122 :
    adaptiveCoverCheck 10 thetaBelowCell11102122 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102122
    e24KC2ThetaBelowLeaf111021220 e24KC2ThetaBelowLeaf111021221 e24KC2ThetaBelowLeaf111021222
      e24KC2ThetaBelowLeaf111021223

theorem e24KC2ThetaBelowNode11102123 :
    adaptiveCoverCheck 10 thetaBelowCell11102123 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102123
    e24KC2ThetaBelowLeaf111021230 e24KC2ThetaBelowLeaf111021231 e24KC2ThetaBelowLeaf111021232
      e24KC2ThetaBelowLeaf111021233

theorem e24KC2ThetaBelowNode11102130 :
    adaptiveCoverCheck 10 thetaBelowCell11102130 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102130
    e24KC2ThetaBelowLeaf111021300 e24KC2ThetaBelowLeaf111021301 e24KC2ThetaBelowLeaf111021302
      e24KC2ThetaBelowLeaf111021303

theorem e24KC2ThetaBelowNode11102131 :
    adaptiveCoverCheck 10 thetaBelowCell11102131 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102131
    e24KC2ThetaBelowLeaf111021310 e24KC2ThetaBelowLeaf111021311 e24KC2ThetaBelowLeaf111021312
      e24KC2ThetaBelowLeaf111021313

theorem e24KC2ThetaBelowNode11102132 :
    adaptiveCoverCheck 10 thetaBelowCell11102132 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102132
    e24KC2ThetaBelowLeaf111021320 e24KC2ThetaBelowLeaf111021321 e24KC2ThetaBelowLeaf111021322
      e24KC2ThetaBelowLeaf111021323

theorem e24KC2ThetaBelowNode11102133 :
    adaptiveCoverCheck 10 thetaBelowCell11102133 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102133
    e24KC2ThetaBelowLeaf111021330 e24KC2ThetaBelowLeaf111021331 e24KC2ThetaBelowLeaf111021332
      e24KC2ThetaBelowLeaf111021333

theorem e24KC2ThetaBelowNode11102200 :
    adaptiveCoverCheck 10 thetaBelowCell11102200 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102200
    e24KC2ThetaBelowLeaf111022000 e24KC2ThetaBelowLeaf111022001 e24KC2ThetaBelowLeaf111022002
      e24KC2ThetaBelowLeaf111022003

theorem e24KC2ThetaBelowNode11102201 :
    adaptiveCoverCheck 10 thetaBelowCell11102201 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102201
    e24KC2ThetaBelowLeaf111022010 e24KC2ThetaBelowLeaf111022011 e24KC2ThetaBelowLeaf111022012
      e24KC2ThetaBelowLeaf111022013

theorem e24KC2ThetaBelowNode11102210 :
    adaptiveCoverCheck 10 thetaBelowCell11102210 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102210
    e24KC2ThetaBelowLeaf111022100 e24KC2ThetaBelowLeaf111022101 e24KC2ThetaBelowLeaf111022102
      e24KC2ThetaBelowLeaf111022103

theorem e24KC2ThetaBelowNode11102211 :
    adaptiveCoverCheck 10 thetaBelowCell11102211 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102211
    e24KC2ThetaBelowLeaf111022110 e24KC2ThetaBelowLeaf111022111 e24KC2ThetaBelowLeaf111022112
      e24KC2ThetaBelowLeaf111022113

theorem e24KC2ThetaBelowNode11102300 :
    adaptiveCoverCheck 10 thetaBelowCell11102300 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102300
    e24KC2ThetaBelowLeaf111023000 e24KC2ThetaBelowLeaf111023001 e24KC2ThetaBelowLeaf111023002
      e24KC2ThetaBelowLeaf111023003

theorem e24KC2ThetaBelowNode11102301 :
    adaptiveCoverCheck 10 thetaBelowCell11102301 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102301
    e24KC2ThetaBelowLeaf111023010 e24KC2ThetaBelowLeaf111023011 e24KC2ThetaBelowLeaf111023012
      e24KC2ThetaBelowLeaf111023013

theorem e24KC2ThetaBelowNode11102310 :
    adaptiveCoverCheck 10 thetaBelowCell11102310 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102310
    e24KC2ThetaBelowLeaf111023100 e24KC2ThetaBelowLeaf111023101 e24KC2ThetaBelowLeaf111023102
      e24KC2ThetaBelowLeaf111023103

theorem e24KC2ThetaBelowNode11102311 :
    adaptiveCoverCheck 10 thetaBelowCell11102311 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102311
    e24KC2ThetaBelowLeaf111023110 e24KC2ThetaBelowLeaf111023111 e24KC2ThetaBelowLeaf111023112
      e24KC2ThetaBelowLeaf111023113

theorem e24KC2ThetaBelowNode11103020 :
    adaptiveCoverCheck 10 thetaBelowCell11103020 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103020
    e24KC2ThetaBelowLeaf111030200 e24KC2ThetaBelowLeaf111030201 e24KC2ThetaBelowLeaf111030202
      e24KC2ThetaBelowLeaf111030203

theorem e24KC2ThetaBelowNode11103021 :
    adaptiveCoverCheck 10 thetaBelowCell11103021 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103021
    e24KC2ThetaBelowLeaf111030210 e24KC2ThetaBelowLeaf111030211 e24KC2ThetaBelowLeaf111030212
      e24KC2ThetaBelowLeaf111030213

theorem e24KC2ThetaBelowNode11103022 :
    adaptiveCoverCheck 10 thetaBelowCell11103022 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103022
    e24KC2ThetaBelowLeaf111030220 e24KC2ThetaBelowLeaf111030221 e24KC2ThetaBelowLeaf111030222
      e24KC2ThetaBelowLeaf111030223

theorem e24KC2ThetaBelowNode11103023 :
    adaptiveCoverCheck 10 thetaBelowCell11103023 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103023
    e24KC2ThetaBelowLeaf111030230 e24KC2ThetaBelowLeaf111030231 e24KC2ThetaBelowLeaf111030232
      e24KC2ThetaBelowLeaf111030233

theorem e24KC2ThetaBelowNode11103030 :
    adaptiveCoverCheck 10 thetaBelowCell11103030 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103030
    e24KC2ThetaBelowLeaf111030300 e24KC2ThetaBelowLeaf111030301 e24KC2ThetaBelowLeaf111030302
      e24KC2ThetaBelowLeaf111030303

theorem e24KC2ThetaBelowNode11103031 :
    adaptiveCoverCheck 10 thetaBelowCell11103031 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103031
    e24KC2ThetaBelowLeaf111030310 e24KC2ThetaBelowLeaf111030311 e24KC2ThetaBelowLeaf111030312
      e24KC2ThetaBelowLeaf111030313

theorem e24KC2ThetaBelowNode11103032 :
    adaptiveCoverCheck 10 thetaBelowCell11103032 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103032
    e24KC2ThetaBelowLeaf111030320 e24KC2ThetaBelowLeaf111030321 e24KC2ThetaBelowLeaf111030322
      e24KC2ThetaBelowLeaf111030323

theorem e24KC2ThetaBelowNode11103033 :
    adaptiveCoverCheck 10 thetaBelowCell11103033 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103033
    e24KC2ThetaBelowLeaf111030330 e24KC2ThetaBelowLeaf111030331 e24KC2ThetaBelowLeaf111030332
      e24KC2ThetaBelowLeaf111030333

theorem e24KC2ThetaBelowNode11103120 :
    adaptiveCoverCheck 10 thetaBelowCell11103120 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103120
    e24KC2ThetaBelowLeaf111031200 e24KC2ThetaBelowLeaf111031201 e24KC2ThetaBelowLeaf111031202
      e24KC2ThetaBelowLeaf111031203

theorem e24KC2ThetaBelowNode11103121 :
    adaptiveCoverCheck 10 thetaBelowCell11103121 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103121
    e24KC2ThetaBelowLeaf111031210 e24KC2ThetaBelowLeaf111031211 e24KC2ThetaBelowLeaf111031212
      e24KC2ThetaBelowLeaf111031213

theorem e24KC2ThetaBelowNode11103122 :
    adaptiveCoverCheck 10 thetaBelowCell11103122 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103122
    e24KC2ThetaBelowLeaf111031220 e24KC2ThetaBelowLeaf111031221 e24KC2ThetaBelowLeaf111031222
      e24KC2ThetaBelowLeaf111031223

theorem e24KC2ThetaBelowNode11103123 :
    adaptiveCoverCheck 10 thetaBelowCell11103123 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103123
    e24KC2ThetaBelowLeaf111031230 e24KC2ThetaBelowLeaf111031231 e24KC2ThetaBelowLeaf111031232
      e24KC2ThetaBelowLeaf111031233

theorem e24KC2ThetaBelowNode11103130 :
    adaptiveCoverCheck 10 thetaBelowCell11103130 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103130
    e24KC2ThetaBelowLeaf111031300 e24KC2ThetaBelowLeaf111031301 e24KC2ThetaBelowLeaf111031302
      e24KC2ThetaBelowLeaf111031303

theorem e24KC2ThetaBelowNode11103131 :
    adaptiveCoverCheck 10 thetaBelowCell11103131 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103131
    e24KC2ThetaBelowLeaf111031310 e24KC2ThetaBelowLeaf111031311 e24KC2ThetaBelowLeaf111031312
      e24KC2ThetaBelowLeaf111031313

theorem e24KC2ThetaBelowNode11103132 :
    adaptiveCoverCheck 10 thetaBelowCell11103132 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103132
    e24KC2ThetaBelowLeaf111031320 e24KC2ThetaBelowLeaf111031321 e24KC2ThetaBelowLeaf111031322
      e24KC2ThetaBelowLeaf111031323

theorem e24KC2ThetaBelowNode11103133 :
    adaptiveCoverCheck 10 thetaBelowCell11103133 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103133
    e24KC2ThetaBelowLeaf111031330 e24KC2ThetaBelowLeaf111031331 e24KC2ThetaBelowLeaf111031332
      e24KC2ThetaBelowLeaf111031333

theorem e24KC2ThetaBelowNode11103200 :
    adaptiveCoverCheck 10 thetaBelowCell11103200 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103200
    e24KC2ThetaBelowLeaf111032000 e24KC2ThetaBelowLeaf111032001 e24KC2ThetaBelowLeaf111032002
      e24KC2ThetaBelowLeaf111032003

theorem e24KC2ThetaBelowNode11103201 :
    adaptiveCoverCheck 10 thetaBelowCell11103201 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103201
    e24KC2ThetaBelowLeaf111032010 e24KC2ThetaBelowLeaf111032011 e24KC2ThetaBelowLeaf111032012
      e24KC2ThetaBelowLeaf111032013

theorem e24KC2ThetaBelowNode11103210 :
    adaptiveCoverCheck 10 thetaBelowCell11103210 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103210
    e24KC2ThetaBelowLeaf111032100 e24KC2ThetaBelowLeaf111032101 e24KC2ThetaBelowLeaf111032102
      e24KC2ThetaBelowLeaf111032103

theorem e24KC2ThetaBelowNode11103211 :
    adaptiveCoverCheck 10 thetaBelowCell11103211 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103211
    e24KC2ThetaBelowLeaf111032110 e24KC2ThetaBelowLeaf111032111 e24KC2ThetaBelowLeaf111032112
      e24KC2ThetaBelowLeaf111032113

theorem e24KC2ThetaBelowNode11103300 :
    adaptiveCoverCheck 10 thetaBelowCell11103300 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103300
    e24KC2ThetaBelowLeaf111033000 e24KC2ThetaBelowLeaf111033001 e24KC2ThetaBelowLeaf111033002
      e24KC2ThetaBelowLeaf111033003

theorem e24KC2ThetaBelowNode11103301 :
    adaptiveCoverCheck 10 thetaBelowCell11103301 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103301
    e24KC2ThetaBelowLeaf111033010 e24KC2ThetaBelowLeaf111033011 e24KC2ThetaBelowLeaf111033012
      e24KC2ThetaBelowLeaf111033013

theorem e24KC2ThetaBelowNode11103310 :
    adaptiveCoverCheck 10 thetaBelowCell11103310 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103310
    e24KC2ThetaBelowLeaf111033100 e24KC2ThetaBelowLeaf111033101 e24KC2ThetaBelowLeaf111033102
      e24KC2ThetaBelowLeaf111033103

theorem e24KC2ThetaBelowNode11103311 :
    adaptiveCoverCheck 10 thetaBelowCell11103311 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103311
    e24KC2ThetaBelowLeaf111033110 e24KC2ThetaBelowLeaf111033111 e24KC2ThetaBelowLeaf111033112
      e24KC2ThetaBelowLeaf111033113

theorem e24KC2ThetaBelowNode11112020 :
    adaptiveCoverCheck 10 thetaBelowCell11112020 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112020
    e24KC2ThetaBelowLeaf111120200 e24KC2ThetaBelowLeaf111120201 e24KC2ThetaBelowLeaf111120202
      e24KC2ThetaBelowLeaf111120203

theorem e24KC2ThetaBelowNode11112021 :
    adaptiveCoverCheck 10 thetaBelowCell11112021 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112021
    e24KC2ThetaBelowLeaf111120210 e24KC2ThetaBelowLeaf111120211 e24KC2ThetaBelowLeaf111120212
      e24KC2ThetaBelowLeaf111120213

theorem e24KC2ThetaBelowNode11112022 :
    adaptiveCoverCheck 10 thetaBelowCell11112022 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112022
    e24KC2ThetaBelowLeaf111120220 e24KC2ThetaBelowLeaf111120221 e24KC2ThetaBelowLeaf111120222
      e24KC2ThetaBelowLeaf111120223

theorem e24KC2ThetaBelowNode11112023 :
    adaptiveCoverCheck 10 thetaBelowCell11112023 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112023
    e24KC2ThetaBelowLeaf111120230 e24KC2ThetaBelowLeaf111120231 e24KC2ThetaBelowLeaf111120232
      e24KC2ThetaBelowLeaf111120233

theorem e24KC2ThetaBelowNode11112030 :
    adaptiveCoverCheck 10 thetaBelowCell11112030 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112030
    e24KC2ThetaBelowLeaf111120300 e24KC2ThetaBelowLeaf111120301 e24KC2ThetaBelowLeaf111120302
      e24KC2ThetaBelowLeaf111120303

theorem e24KC2ThetaBelowNode11112031 :
    adaptiveCoverCheck 10 thetaBelowCell11112031 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112031
    e24KC2ThetaBelowLeaf111120310 e24KC2ThetaBelowLeaf111120311 e24KC2ThetaBelowLeaf111120312
      e24KC2ThetaBelowLeaf111120313

theorem e24KC2ThetaBelowNode11112032 :
    adaptiveCoverCheck 10 thetaBelowCell11112032 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112032
    e24KC2ThetaBelowLeaf111120320 e24KC2ThetaBelowLeaf111120321 e24KC2ThetaBelowLeaf111120322
      e24KC2ThetaBelowLeaf111120323

theorem e24KC2ThetaBelowNode11112033 :
    adaptiveCoverCheck 10 thetaBelowCell11112033 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112033
    e24KC2ThetaBelowLeaf111120330 e24KC2ThetaBelowLeaf111120331 e24KC2ThetaBelowLeaf111120332
      e24KC2ThetaBelowLeaf111120333

theorem e24KC2ThetaBelowNode11112120 :
    adaptiveCoverCheck 10 thetaBelowCell11112120 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112120
    e24KC2ThetaBelowLeaf111121200 e24KC2ThetaBelowLeaf111121201 e24KC2ThetaBelowLeaf111121202
      e24KC2ThetaBelowLeaf111121203

theorem e24KC2ThetaBelowNode11112121 :
    adaptiveCoverCheck 10 thetaBelowCell11112121 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112121
    e24KC2ThetaBelowLeaf111121210 e24KC2ThetaBelowLeaf111121211 e24KC2ThetaBelowLeaf111121212
      e24KC2ThetaBelowLeaf111121213

theorem e24KC2ThetaBelowNode11112122 :
    adaptiveCoverCheck 10 thetaBelowCell11112122 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112122
    e24KC2ThetaBelowLeaf111121220 e24KC2ThetaBelowLeaf111121221 e24KC2ThetaBelowLeaf111121222
      e24KC2ThetaBelowLeaf111121223

theorem e24KC2ThetaBelowNode11112123 :
    adaptiveCoverCheck 10 thetaBelowCell11112123 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112123
    e24KC2ThetaBelowLeaf111121230 e24KC2ThetaBelowLeaf111121231 e24KC2ThetaBelowLeaf111121232
      e24KC2ThetaBelowLeaf111121233

theorem e24KC2ThetaBelowNode11112130 :
    adaptiveCoverCheck 10 thetaBelowCell11112130 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112130
    e24KC2ThetaBelowLeaf111121300 e24KC2ThetaBelowLeaf111121301 e24KC2ThetaBelowLeaf111121302
      e24KC2ThetaBelowLeaf111121303

theorem e24KC2ThetaBelowNode11112132 :
    adaptiveCoverCheck 10 thetaBelowCell11112132 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112132
    e24KC2ThetaBelowLeaf111121320 e24KC2ThetaBelowLeaf111121321 e24KC2ThetaBelowLeaf111121322
      e24KC2ThetaBelowLeaf111121323

theorem e24KC2ThetaBelowNode11112133 :
    adaptiveCoverCheck 10 thetaBelowCell11112133 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112133
    e24KC2ThetaBelowLeaf111121330 e24KC2ThetaBelowLeaf111121331 e24KC2ThetaBelowLeaf111121332
      e24KC2ThetaBelowLeaf111121333

theorem e24KC2ThetaBelowNode11112200 :
    adaptiveCoverCheck 10 thetaBelowCell11112200 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112200
    e24KC2ThetaBelowLeaf111122000 e24KC2ThetaBelowLeaf111122001 e24KC2ThetaBelowLeaf111122002
      e24KC2ThetaBelowLeaf111122003

theorem e24KC2ThetaBelowNode11112201 :
    adaptiveCoverCheck 10 thetaBelowCell11112201 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112201
    e24KC2ThetaBelowLeaf111122010 e24KC2ThetaBelowLeaf111122011 e24KC2ThetaBelowLeaf111122012
      e24KC2ThetaBelowLeaf111122013

theorem e24KC2ThetaBelowNode11112210 :
    adaptiveCoverCheck 10 thetaBelowCell11112210 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112210
    e24KC2ThetaBelowLeaf111122100 e24KC2ThetaBelowLeaf111122101 e24KC2ThetaBelowLeaf111122102
      e24KC2ThetaBelowLeaf111122103

theorem e24KC2ThetaBelowNode11112211 :
    adaptiveCoverCheck 10 thetaBelowCell11112211 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112211
    e24KC2ThetaBelowLeaf111122110 e24KC2ThetaBelowLeaf111122111 e24KC2ThetaBelowLeaf111122112
      e24KC2ThetaBelowLeaf111122113

theorem e24KC2ThetaBelowNode11112212 :
    adaptiveCoverCheck 10 thetaBelowCell11112212 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112212
    e24KC2ThetaBelowLeaf111122120 e24KC2ThetaBelowLeaf111122121 e24KC2ThetaBelowLeaf111122122
      e24KC2ThetaBelowLeaf111122123

theorem e24KC2ThetaBelowNode11112213 :
    adaptiveCoverCheck 10 thetaBelowCell11112213 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112213
    e24KC2ThetaBelowLeaf111122130 e24KC2ThetaBelowLeaf111122131 e24KC2ThetaBelowLeaf111122132
      e24KC2ThetaBelowLeaf111122133

theorem e24KC2ThetaBelowNode11112300 :
    adaptiveCoverCheck 10 thetaBelowCell11112300 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112300
    e24KC2ThetaBelowLeaf111123000 e24KC2ThetaBelowLeaf111123001 e24KC2ThetaBelowLeaf111123002
      e24KC2ThetaBelowLeaf111123003

theorem e24KC2ThetaBelowNode11112301 :
    adaptiveCoverCheck 10 thetaBelowCell11112301 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112301
    e24KC2ThetaBelowLeaf111123010 e24KC2ThetaBelowLeaf111123011 e24KC2ThetaBelowLeaf111123012
      e24KC2ThetaBelowLeaf111123013

theorem e24KC2ThetaBelowNode11112302 :
    adaptiveCoverCheck 10 thetaBelowCell11112302 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112302
    e24KC2ThetaBelowLeaf111123020 e24KC2ThetaBelowLeaf111123021 e24KC2ThetaBelowLeaf111123022
      e24KC2ThetaBelowLeaf111123023

theorem e24KC2ThetaBelowNode11112303 :
    adaptiveCoverCheck 10 thetaBelowCell11112303 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112303
    e24KC2ThetaBelowLeaf111123030 e24KC2ThetaBelowLeaf111123031 e24KC2ThetaBelowLeaf111123032
      e24KC2ThetaBelowLeaf111123033

theorem e24KC2ThetaBelowNode11112310 :
    adaptiveCoverCheck 10 thetaBelowCell11112310 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112310
    e24KC2ThetaBelowLeaf111123100 e24KC2ThetaBelowLeaf111123101 e24KC2ThetaBelowLeaf111123102
      e24KC2ThetaBelowLeaf111123103

theorem e24KC2ThetaBelowNode11112311 :
    adaptiveCoverCheck 10 thetaBelowCell11112311 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112311
    e24KC2ThetaBelowLeaf111123110 e24KC2ThetaBelowLeaf111123111 e24KC2ThetaBelowLeaf111123112
      e24KC2ThetaBelowLeaf111123113

theorem e24KC2ThetaBelowNode11112312 :
    adaptiveCoverCheck 10 thetaBelowCell11112312 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112312
    e24KC2ThetaBelowLeaf111123120 e24KC2ThetaBelowLeaf111123121 e24KC2ThetaBelowLeaf111123122
      e24KC2ThetaBelowLeaf111123123

theorem e24KC2ThetaBelowNode11112313 :
    adaptiveCoverCheck 10 thetaBelowCell11112313 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112313
    e24KC2ThetaBelowLeaf111123130 e24KC2ThetaBelowLeaf111123131 e24KC2ThetaBelowLeaf111123132
      e24KC2ThetaBelowLeaf111123133

theorem e24KC2ThetaBelowNode11113022 :
    adaptiveCoverCheck 10 thetaBelowCell11113022 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113022
    e24KC2ThetaBelowLeaf111130220 e24KC2ThetaBelowLeaf111130221 e24KC2ThetaBelowLeaf111130222
      e24KC2ThetaBelowLeaf111130223

theorem e24KC2ThetaBelowNode11113023 :
    adaptiveCoverCheck 10 thetaBelowCell11113023 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113023
    e24KC2ThetaBelowLeaf111130230 e24KC2ThetaBelowLeaf111130231 e24KC2ThetaBelowLeaf111130232
      e24KC2ThetaBelowLeaf111130233

theorem e24KC2ThetaBelowNode11113032 :
    adaptiveCoverCheck 10 thetaBelowCell11113032 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113032
    e24KC2ThetaBelowLeaf111130320 e24KC2ThetaBelowLeaf111130321 e24KC2ThetaBelowLeaf111130322
      e24KC2ThetaBelowLeaf111130323

theorem e24KC2ThetaBelowNode11113033 :
    adaptiveCoverCheck 10 thetaBelowCell11113033 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113033
    e24KC2ThetaBelowLeaf111130330 e24KC2ThetaBelowLeaf111130331 e24KC2ThetaBelowLeaf111130332
      e24KC2ThetaBelowLeaf111130333

theorem e24KC2ThetaBelowNode11113122 :
    adaptiveCoverCheck 10 thetaBelowCell11113122 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113122
    e24KC2ThetaBelowLeaf111131220 e24KC2ThetaBelowLeaf111131221 e24KC2ThetaBelowLeaf111131222
      e24KC2ThetaBelowLeaf111131223

theorem e24KC2ThetaBelowNode11113123 :
    adaptiveCoverCheck 10 thetaBelowCell11113123 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113123
    e24KC2ThetaBelowLeaf111131230 e24KC2ThetaBelowLeaf111131231 e24KC2ThetaBelowLeaf111131232
      e24KC2ThetaBelowLeaf111131233

theorem e24KC2ThetaBelowNode11113132 :
    adaptiveCoverCheck 10 thetaBelowCell11113132 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113132
    e24KC2ThetaBelowLeaf111131320 e24KC2ThetaBelowLeaf111131321 e24KC2ThetaBelowLeaf111131322
      e24KC2ThetaBelowLeaf111131323

theorem e24KC2ThetaBelowNode11113133 :
    adaptiveCoverCheck 10 thetaBelowCell11113133 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113133
    e24KC2ThetaBelowLeaf111131330 e24KC2ThetaBelowLeaf111131331 e24KC2ThetaBelowLeaf111131332
      e24KC2ThetaBelowLeaf111131333

theorem e24KC2ThetaBelowNode11113200 :
    adaptiveCoverCheck 10 thetaBelowCell11113200 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113200
    e24KC2ThetaBelowLeaf111132000 e24KC2ThetaBelowLeaf111132001 e24KC2ThetaBelowLeaf111132002
      e24KC2ThetaBelowLeaf111132003

theorem e24KC2ThetaBelowNode11113201 :
    adaptiveCoverCheck 10 thetaBelowCell11113201 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113201
    e24KC2ThetaBelowLeaf111132010 e24KC2ThetaBelowLeaf111132011 e24KC2ThetaBelowLeaf111132012
      e24KC2ThetaBelowLeaf111132013

theorem e24KC2ThetaBelowNode11113202 :
    adaptiveCoverCheck 10 thetaBelowCell11113202 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113202
    e24KC2ThetaBelowLeaf111132020 e24KC2ThetaBelowLeaf111132021 e24KC2ThetaBelowLeaf111132022
      e24KC2ThetaBelowLeaf111132023

theorem e24KC2ThetaBelowNode11113203 :
    adaptiveCoverCheck 10 thetaBelowCell11113203 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113203
    e24KC2ThetaBelowLeaf111132030 e24KC2ThetaBelowLeaf111132031 e24KC2ThetaBelowLeaf111132032
      e24KC2ThetaBelowLeaf111132033

theorem e24KC2ThetaBelowNode11113210 :
    adaptiveCoverCheck 10 thetaBelowCell11113210 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113210
    e24KC2ThetaBelowLeaf111132100 e24KC2ThetaBelowLeaf111132101 e24KC2ThetaBelowLeaf111132102
      e24KC2ThetaBelowLeaf111132103

theorem e24KC2ThetaBelowNode11113211 :
    adaptiveCoverCheck 10 thetaBelowCell11113211 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113211
    e24KC2ThetaBelowLeaf111132110 e24KC2ThetaBelowLeaf111132111 e24KC2ThetaBelowLeaf111132112
      e24KC2ThetaBelowLeaf111132113

theorem e24KC2ThetaBelowNode11113212 :
    adaptiveCoverCheck 10 thetaBelowCell11113212 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113212
    e24KC2ThetaBelowLeaf111132120 e24KC2ThetaBelowLeaf111132121 e24KC2ThetaBelowLeaf111132122
      e24KC2ThetaBelowLeaf111132123

theorem e24KC2ThetaBelowNode11113213 :
    adaptiveCoverCheck 10 thetaBelowCell11113213 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113213
    e24KC2ThetaBelowLeaf111132130 e24KC2ThetaBelowLeaf111132131 e24KC2ThetaBelowLeaf111132132
      e24KC2ThetaBelowLeaf111132133

theorem e24KC2ThetaBelowNode11113300 :
    adaptiveCoverCheck 10 thetaBelowCell11113300 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113300
    e24KC2ThetaBelowLeaf111133000 e24KC2ThetaBelowLeaf111133001 e24KC2ThetaBelowLeaf111133002
      e24KC2ThetaBelowLeaf111133003

theorem e24KC2ThetaBelowNode11113301 :
    adaptiveCoverCheck 10 thetaBelowCell11113301 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113301
    e24KC2ThetaBelowLeaf111133010 e24KC2ThetaBelowLeaf111133011 e24KC2ThetaBelowLeaf111133012
      e24KC2ThetaBelowLeaf111133013

theorem e24KC2ThetaBelowNode11113302 :
    adaptiveCoverCheck 10 thetaBelowCell11113302 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113302
    e24KC2ThetaBelowLeaf111133020 e24KC2ThetaBelowLeaf111133021 e24KC2ThetaBelowLeaf111133022
      e24KC2ThetaBelowLeaf111133023

theorem e24KC2ThetaBelowNode11113303 :
    adaptiveCoverCheck 10 thetaBelowCell11113303 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113303
    e24KC2ThetaBelowLeaf111133030 e24KC2ThetaBelowLeaf111133031 e24KC2ThetaBelowLeaf111133032
      e24KC2ThetaBelowLeaf111133033

theorem e24KC2ThetaBelowNode11113310 :
    adaptiveCoverCheck 10 thetaBelowCell11113310 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113310
    e24KC2ThetaBelowLeaf111133100 e24KC2ThetaBelowLeaf111133101 e24KC2ThetaBelowLeaf111133102
      e24KC2ThetaBelowLeaf111133103

theorem e24KC2ThetaBelowNode11113311 :
    adaptiveCoverCheck 10 thetaBelowCell11113311 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113311
    e24KC2ThetaBelowLeaf111133110 e24KC2ThetaBelowLeaf111133111 e24KC2ThetaBelowLeaf111133112
      e24KC2ThetaBelowLeaf111133113

theorem e24KC2ThetaBelowNode11113312 :
    adaptiveCoverCheck 10 thetaBelowCell11113312 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113312
    e24KC2ThetaBelowLeaf111133120 e24KC2ThetaBelowLeaf111133121 e24KC2ThetaBelowLeaf111133122
      e24KC2ThetaBelowLeaf111133123

theorem e24KC2ThetaBelowNode11113313 :
    adaptiveCoverCheck 10 thetaBelowCell11113313 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113313
    e24KC2ThetaBelowLeaf111133130 e24KC2ThetaBelowLeaf111133131 e24KC2ThetaBelowLeaf111133132
      e24KC2ThetaBelowLeaf111133133

theorem e24KC2ThetaBelowNode1011303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH thetaBelowCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHH thetaBelowCell1011)))
    e24KC2ThetaBelowLeaf10113030 e24KC2ThetaBelowLeaf10113031 e24KC2ThetaBelowLeaf10113032
      e24KC2ThetaBelowLeaf10113033

theorem e24KC2ThetaBelowNode1011311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH thetaBelowCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHH thetaBelowCell1011)))
    e24KC2ThetaBelowLeaf10113110 e24KC2ThetaBelowLeaf10113111 e24KC2ThetaBelowLeaf10113112
      e24KC2ThetaBelowLeaf10113113

theorem e24KC2ThetaBelowNode1011312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH thetaBelowCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHH thetaBelowCell1011)))
    e24KC2ThetaBelowLeaf10113120 e24KC2ThetaBelowLeaf10113121 e24KC2ThetaBelowLeaf10113122
      e24KC2ThetaBelowLeaf10113123

theorem e24KC2ThetaBelowNode1011313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH thetaBelowCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHH thetaBelowCell1011)))
    e24KC2ThetaBelowLeaf10113130 e24KC2ThetaBelowLeaf10113131 e24KC2ThetaBelowLeaf10113132
      e24KC2ThetaBelowLeaf10113133

theorem e24KC2ThetaBelowNode1100032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHH (childLL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11000320 e24KC2ThetaBelowLeaf11000321 e24KC2ThetaBelowLeaf11000322
      e24KC2ThetaBelowLeaf11000323

theorem e24KC2ThetaBelowNode1100033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHH (childLL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11000330 e24KC2ThetaBelowLeaf11000331 e24KC2ThetaBelowLeaf11000332
      e24KC2ThetaBelowLeaf11000333

theorem e24KC2ThetaBelowNode1100122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHL (childLH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11001220 e24KC2ThetaBelowLeaf11001221 e24KC2ThetaBelowLeaf11001222
      e24KC2ThetaBelowLeaf11001223

theorem e24KC2ThetaBelowNode1100123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHL (childLH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11001230 e24KC2ThetaBelowLeaf11001231 e24KC2ThetaBelowLeaf11001232
      e24KC2ThetaBelowLeaf11001233

theorem e24KC2ThetaBelowNode1100132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHH (childLH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11001320 e24KC2ThetaBelowLeaf11001321 e24KC2ThetaBelowLeaf11001322
      e24KC2ThetaBelowLeaf11001323

theorem e24KC2ThetaBelowNode1100133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHH (childLH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11001330 e24KC2ThetaBelowLeaf11001331 e24KC2ThetaBelowLeaf11001332
      e24KC2ThetaBelowLeaf11001333

theorem e24KC2ThetaBelowNode1100200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002000 e24KC2ThetaBelowLeaf11002001 e24KC2ThetaBelowLeaf11002002
      e24KC2ThetaBelowLeaf11002003

theorem e24KC2ThetaBelowNode1100201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002010 e24KC2ThetaBelowLeaf11002011 e24KC2ThetaBelowLeaf11002012
      e24KC2ThetaBelowLeaf11002013

theorem e24KC2ThetaBelowNode1100202 :
    adaptiveCoverCheck 11 (childHL (childLL (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002020 e24KC2ThetaBelowLeaf11002021 e24KC2ThetaBelowLeaf11002022
      e24KC2ThetaBelowLeaf11002023

theorem e24KC2ThetaBelowNode1100203 :
    adaptiveCoverCheck 11 (childHH (childLL (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002030 e24KC2ThetaBelowLeaf11002031 e24KC2ThetaBelowLeaf11002032
      e24KC2ThetaBelowLeaf11002033

theorem e24KC2ThetaBelowNode1100210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002100 e24KC2ThetaBelowLeaf11002101 e24KC2ThetaBelowLeaf11002102
      e24KC2ThetaBelowLeaf11002103

theorem e24KC2ThetaBelowNode1100211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002110 e24KC2ThetaBelowLeaf11002111 e24KC2ThetaBelowLeaf11002112
      e24KC2ThetaBelowLeaf11002113

theorem e24KC2ThetaBelowNode1100212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002120 e24KC2ThetaBelowLeaf11002121 e24KC2ThetaBelowLeaf11002122
      e24KC2ThetaBelowLeaf11002123

theorem e24KC2ThetaBelowNode1100213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002130 e24KC2ThetaBelowLeaf11002131 e24KC2ThetaBelowLeaf11002132
      e24KC2ThetaBelowLeaf11002133

theorem e24KC2ThetaBelowNode1100300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003000 e24KC2ThetaBelowLeaf11003001 e24KC2ThetaBelowLeaf11003002
      e24KC2ThetaBelowLeaf11003003

theorem e24KC2ThetaBelowNode1100301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003010 e24KC2ThetaBelowLeaf11003011 e24KC2ThetaBelowLeaf11003012
      e24KC2ThetaBelowLeaf11003013

theorem e24KC2ThetaBelowNode1100302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003020 e24KC2ThetaBelowLeaf11003021 e24KC2ThetaBelowLeaf11003022
      e24KC2ThetaBelowLeaf11003023

theorem e24KC2ThetaBelowNode1100303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003030 e24KC2ThetaBelowLeaf11003031 e24KC2ThetaBelowLeaf11003032
      e24KC2ThetaBelowLeaf11003033

theorem e24KC2ThetaBelowNode1100310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003100 e24KC2ThetaBelowLeaf11003101 e24KC2ThetaBelowLeaf11003102
      e24KC2ThetaBelowLeaf11003103

theorem e24KC2ThetaBelowNode1100311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003110 e24KC2ThetaBelowLeaf11003111 e24KC2ThetaBelowLeaf11003112
      e24KC2ThetaBelowLeaf11003113

theorem e24KC2ThetaBelowNode1100312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003120 e24KC2ThetaBelowLeaf11003121 e24KC2ThetaBelowLeaf11003122
      e24KC2ThetaBelowLeaf11003123

theorem e24KC2ThetaBelowNode1100313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003130 e24KC2ThetaBelowLeaf11003131 e24KC2ThetaBelowLeaf11003132
      e24KC2ThetaBelowLeaf11003133

theorem e24KC2ThetaBelowNode1100330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003300 e24KC2ThetaBelowLeaf11003301 e24KC2ThetaBelowLeaf11003302
      e24KC2ThetaBelowLeaf11003303

theorem e24KC2ThetaBelowNode1100331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003310 e24KC2ThetaBelowLeaf11003311 e24KC2ThetaBelowLeaf11003312
      e24KC2ThetaBelowLeaf11003313

theorem e24KC2ThetaBelowNode1101022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHL (childLL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11010220 e24KC2ThetaBelowLeaf11010221 e24KC2ThetaBelowLeaf11010222
      e24KC2ThetaBelowLeaf11010223

theorem e24KC2ThetaBelowNode1101023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHL (childLL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11010230 e24KC2ThetaBelowLeaf11010231 e24KC2ThetaBelowLeaf11010232
      e24KC2ThetaBelowLeaf11010233

theorem e24KC2ThetaBelowNode1101200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012000 e24KC2ThetaBelowLeaf11012001 e24KC2ThetaBelowLeaf11012002
      e24KC2ThetaBelowLeaf11012003

theorem e24KC2ThetaBelowNode1101201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012010 e24KC2ThetaBelowLeaf11012011 e24KC2ThetaBelowLeaf11012012
      e24KC2ThetaBelowLeaf11012013

theorem e24KC2ThetaBelowNode1101202 :
    adaptiveCoverCheck 11 (childHL (childLL (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012020 e24KC2ThetaBelowLeaf11012021 e24KC2ThetaBelowLeaf11012022
      e24KC2ThetaBelowLeaf11012023

theorem e24KC2ThetaBelowNode1101203 :
    adaptiveCoverCheck 11 (childHH (childLL (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012030 e24KC2ThetaBelowLeaf11012031 e24KC2ThetaBelowLeaf11012032
      e24KC2ThetaBelowLeaf11012033

theorem e24KC2ThetaBelowNode1101210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012100 e24KC2ThetaBelowLeaf11012101 e24KC2ThetaBelowLeaf11012102
      e24KC2ThetaBelowLeaf11012103

theorem e24KC2ThetaBelowNode1101211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012110 e24KC2ThetaBelowLeaf11012111 e24KC2ThetaBelowLeaf11012112
      e24KC2ThetaBelowLeaf11012113

theorem e24KC2ThetaBelowNode1101212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012120 e24KC2ThetaBelowLeaf11012121 e24KC2ThetaBelowLeaf11012122
      e24KC2ThetaBelowLeaf11012123

theorem e24KC2ThetaBelowNode1101213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012130 e24KC2ThetaBelowLeaf11012131 e24KC2ThetaBelowNode11012132
      e24KC2ThetaBelowNode11012133

theorem e24KC2ThetaBelowNode1101220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHL (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012200 e24KC2ThetaBelowLeaf11012201 e24KC2ThetaBelowLeaf11012202
      e24KC2ThetaBelowLeaf11012203

theorem e24KC2ThetaBelowNode1101221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHL (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012210 e24KC2ThetaBelowLeaf11012211 e24KC2ThetaBelowLeaf11012212
      e24KC2ThetaBelowLeaf11012213

theorem e24KC2ThetaBelowNode1101230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012300 e24KC2ThetaBelowLeaf11012301 e24KC2ThetaBelowLeaf11012302
      e24KC2ThetaBelowLeaf11012303

theorem e24KC2ThetaBelowNode1101231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012310 e24KC2ThetaBelowLeaf11012311 e24KC2ThetaBelowLeaf11012312
      e24KC2ThetaBelowLeaf11012313

theorem e24KC2ThetaBelowNode1101300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013000 e24KC2ThetaBelowLeaf11013001 e24KC2ThetaBelowLeaf11013002
      e24KC2ThetaBelowLeaf11013003

theorem e24KC2ThetaBelowNode1101301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013010 e24KC2ThetaBelowLeaf11013011 e24KC2ThetaBelowLeaf11013012
      e24KC2ThetaBelowNode11013013

theorem e24KC2ThetaBelowNode1101302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013020 e24KC2ThetaBelowNode11013021 e24KC2ThetaBelowNode11013022
      e24KC2ThetaBelowNode11013023

theorem e24KC2ThetaBelowNode1101303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowNode11013030 e24KC2ThetaBelowNode11013031 e24KC2ThetaBelowNode11013032
      e24KC2ThetaBelowNode11013033

theorem e24KC2ThetaBelowNode1101310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013100 e24KC2ThetaBelowLeaf11013101 e24KC2ThetaBelowNode11013102
      e24KC2ThetaBelowNode11013103

theorem e24KC2ThetaBelowNode1101311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013110 e24KC2ThetaBelowLeaf11013111 e24KC2ThetaBelowNode11013112
      e24KC2ThetaBelowNode11013113

theorem e24KC2ThetaBelowNode1101312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowNode11013120 e24KC2ThetaBelowNode11013121 e24KC2ThetaBelowNode11013122
      e24KC2ThetaBelowNode11013123

theorem e24KC2ThetaBelowNode1101313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowNode11013130 e24KC2ThetaBelowNode11013131 e24KC2ThetaBelowNode11013132
      e24KC2ThetaBelowNode11013133

theorem e24KC2ThetaBelowNode1101320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHL (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013200 e24KC2ThetaBelowLeaf11013201 e24KC2ThetaBelowLeaf11013202
      e24KC2ThetaBelowLeaf11013203

theorem e24KC2ThetaBelowNode1101321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHL (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013210 e24KC2ThetaBelowLeaf11013211 e24KC2ThetaBelowLeaf11013212
      e24KC2ThetaBelowLeaf11013213

theorem e24KC2ThetaBelowNode1101330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013300 e24KC2ThetaBelowLeaf11013301 e24KC2ThetaBelowLeaf11013302
      e24KC2ThetaBelowLeaf11013303

theorem e24KC2ThetaBelowNode1101331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013310 e24KC2ThetaBelowLeaf11013311 e24KC2ThetaBelowLeaf11013312
      e24KC2ThetaBelowLeaf11013313

theorem e24KC2ThetaBelowNode1110200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11102000 e24KC2ThetaBelowLeaf11102001 e24KC2ThetaBelowNode11102002
      e24KC2ThetaBelowNode11102003

theorem e24KC2ThetaBelowNode1110201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11102010 e24KC2ThetaBelowLeaf11102011 e24KC2ThetaBelowNode11102012
      e24KC2ThetaBelowNode11102013

theorem e24KC2ThetaBelowNode1110202 :
    adaptiveCoverCheck 11 (childHL (childLL (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102020 e24KC2ThetaBelowNode11102021 e24KC2ThetaBelowNode11102022
      e24KC2ThetaBelowNode11102023

theorem e24KC2ThetaBelowNode1110203 :
    adaptiveCoverCheck 11 (childHH (childLL (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102030 e24KC2ThetaBelowNode11102031 e24KC2ThetaBelowNode11102032
      e24KC2ThetaBelowNode11102033

theorem e24KC2ThetaBelowNode1110210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11102100 e24KC2ThetaBelowLeaf11102101 e24KC2ThetaBelowLeaf11102102
      e24KC2ThetaBelowLeaf11102103

theorem e24KC2ThetaBelowNode1110211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11102110 e24KC2ThetaBelowLeaf11102111 e24KC2ThetaBelowLeaf11102112
      e24KC2ThetaBelowLeaf11102113

theorem e24KC2ThetaBelowNode1110212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102120 e24KC2ThetaBelowNode11102121 e24KC2ThetaBelowNode11102122
      e24KC2ThetaBelowNode11102123

theorem e24KC2ThetaBelowNode1110213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102130 e24KC2ThetaBelowNode11102131 e24KC2ThetaBelowNode11102132
      e24KC2ThetaBelowNode11102133

theorem e24KC2ThetaBelowNode1110220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHL (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102200 e24KC2ThetaBelowNode11102201 e24KC2ThetaBelowLeaf11102202
      e24KC2ThetaBelowLeaf11102203

theorem e24KC2ThetaBelowNode1110221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHL (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102210 e24KC2ThetaBelowNode11102211 e24KC2ThetaBelowLeaf11102212
      e24KC2ThetaBelowLeaf11102213

theorem e24KC2ThetaBelowNode1110230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102300 e24KC2ThetaBelowNode11102301 e24KC2ThetaBelowLeaf11102302
      e24KC2ThetaBelowLeaf11102303

theorem e24KC2ThetaBelowNode1110231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102310 e24KC2ThetaBelowNode11102311 e24KC2ThetaBelowLeaf11102312
      e24KC2ThetaBelowLeaf11102313

theorem e24KC2ThetaBelowNode1110300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11103000 e24KC2ThetaBelowLeaf11103001 e24KC2ThetaBelowLeaf11103002
      e24KC2ThetaBelowLeaf11103003

theorem e24KC2ThetaBelowNode1110301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11103010 e24KC2ThetaBelowLeaf11103011 e24KC2ThetaBelowLeaf11103012
      e24KC2ThetaBelowLeaf11103013

theorem e24KC2ThetaBelowNode1110302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103020 e24KC2ThetaBelowNode11103021 e24KC2ThetaBelowNode11103022
      e24KC2ThetaBelowNode11103023

theorem e24KC2ThetaBelowNode1110303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103030 e24KC2ThetaBelowNode11103031 e24KC2ThetaBelowNode11103032
      e24KC2ThetaBelowNode11103033

theorem e24KC2ThetaBelowNode1110310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11103100 e24KC2ThetaBelowLeaf11103101 e24KC2ThetaBelowLeaf11103102
      e24KC2ThetaBelowLeaf11103103

theorem e24KC2ThetaBelowNode1110311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11103110 e24KC2ThetaBelowLeaf11103111 e24KC2ThetaBelowLeaf11103112
      e24KC2ThetaBelowLeaf11103113

theorem e24KC2ThetaBelowNode1110312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103120 e24KC2ThetaBelowNode11103121 e24KC2ThetaBelowNode11103122
      e24KC2ThetaBelowNode11103123

theorem e24KC2ThetaBelowNode1110313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103130 e24KC2ThetaBelowNode11103131 e24KC2ThetaBelowNode11103132
      e24KC2ThetaBelowNode11103133

theorem e24KC2ThetaBelowNode1110320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHL (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103200 e24KC2ThetaBelowNode11103201 e24KC2ThetaBelowLeaf11103202
      e24KC2ThetaBelowLeaf11103203

theorem e24KC2ThetaBelowNode1110321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHL (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103210 e24KC2ThetaBelowNode11103211 e24KC2ThetaBelowLeaf11103212
      e24KC2ThetaBelowLeaf11103213

theorem e24KC2ThetaBelowNode1110330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103300 e24KC2ThetaBelowNode11103301 e24KC2ThetaBelowLeaf11103302
      e24KC2ThetaBelowLeaf11103303

theorem e24KC2ThetaBelowNode1110331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103310 e24KC2ThetaBelowNode11103311 e24KC2ThetaBelowLeaf11103312
      e24KC2ThetaBelowLeaf11103313

theorem e24KC2ThetaBelowNode1111200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112000 e24KC2ThetaBelowLeaf11112001 e24KC2ThetaBelowLeaf11112002
      e24KC2ThetaBelowLeaf11112003

theorem e24KC2ThetaBelowNode1111201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112010 e24KC2ThetaBelowLeaf11112011 e24KC2ThetaBelowLeaf11112012
      e24KC2ThetaBelowLeaf11112013

theorem e24KC2ThetaBelowNode1111202 :
    adaptiveCoverCheck 11 (childHL (childLL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112020 e24KC2ThetaBelowNode11112021 e24KC2ThetaBelowNode11112022
      e24KC2ThetaBelowNode11112023

theorem e24KC2ThetaBelowNode1111203 :
    adaptiveCoverCheck 11 (childHH (childLL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112030 e24KC2ThetaBelowNode11112031 e24KC2ThetaBelowNode11112032
      e24KC2ThetaBelowNode11112033

theorem e24KC2ThetaBelowNode1111210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112100 e24KC2ThetaBelowLeaf11112101 e24KC2ThetaBelowLeaf11112102
      e24KC2ThetaBelowLeaf11112103

theorem e24KC2ThetaBelowNode1111211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112110 e24KC2ThetaBelowLeaf11112111 e24KC2ThetaBelowLeaf11112112
      e24KC2ThetaBelowLeaf11112113

theorem e24KC2ThetaBelowNode1111212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112120 e24KC2ThetaBelowNode11112121 e24KC2ThetaBelowNode11112122
      e24KC2ThetaBelowNode11112123

theorem e24KC2ThetaBelowNode1111213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112130 e24KC2ThetaBelowLeaf11112131 e24KC2ThetaBelowNode11112132
      e24KC2ThetaBelowNode11112133

theorem e24KC2ThetaBelowNode1111220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112200 e24KC2ThetaBelowNode11112201 e24KC2ThetaBelowLeaf11112202
      e24KC2ThetaBelowLeaf11112203

theorem e24KC2ThetaBelowNode1111221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112210 e24KC2ThetaBelowNode11112211 e24KC2ThetaBelowNode11112212
      e24KC2ThetaBelowNode11112213

theorem e24KC2ThetaBelowNode1111222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112220 e24KC2ThetaBelowLeaf11112221 e24KC2ThetaBelowLeaf11112222
      e24KC2ThetaBelowLeaf11112223

theorem e24KC2ThetaBelowNode1111223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112230 e24KC2ThetaBelowLeaf11112231 e24KC2ThetaBelowLeaf11112232
      e24KC2ThetaBelowLeaf11112233

theorem e24KC2ThetaBelowNode1111230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112300 e24KC2ThetaBelowNode11112301 e24KC2ThetaBelowNode11112302
      e24KC2ThetaBelowNode11112303

theorem e24KC2ThetaBelowNode1111231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112310 e24KC2ThetaBelowNode11112311 e24KC2ThetaBelowNode11112312
      e24KC2ThetaBelowNode11112313

theorem e24KC2ThetaBelowNode1111232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112320 e24KC2ThetaBelowLeaf11112321 e24KC2ThetaBelowLeaf11112322
      e24KC2ThetaBelowLeaf11112323

theorem e24KC2ThetaBelowNode1111233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112330 e24KC2ThetaBelowLeaf11112331 e24KC2ThetaBelowLeaf11112332
      e24KC2ThetaBelowLeaf11112333

theorem e24KC2ThetaBelowNode1111302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113020 e24KC2ThetaBelowLeaf11113021 e24KC2ThetaBelowNode11113022
      e24KC2ThetaBelowNode11113023

theorem e24KC2ThetaBelowNode1111303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113030 e24KC2ThetaBelowLeaf11113031 e24KC2ThetaBelowNode11113032
      e24KC2ThetaBelowNode11113033

theorem e24KC2ThetaBelowNode1111312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113120 e24KC2ThetaBelowLeaf11113121 e24KC2ThetaBelowNode11113122
      e24KC2ThetaBelowNode11113123

theorem e24KC2ThetaBelowNode1111313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113130 e24KC2ThetaBelowLeaf11113131 e24KC2ThetaBelowNode11113132
      e24KC2ThetaBelowNode11113133

theorem e24KC2ThetaBelowNode1111320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHL (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowNode11113200 e24KC2ThetaBelowNode11113201 e24KC2ThetaBelowNode11113202
      e24KC2ThetaBelowNode11113203

theorem e24KC2ThetaBelowNode1111321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHL (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowNode11113210 e24KC2ThetaBelowNode11113211 e24KC2ThetaBelowNode11113212
      e24KC2ThetaBelowNode11113213

theorem e24KC2ThetaBelowNode1111322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHL (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113220 e24KC2ThetaBelowLeaf11113221 e24KC2ThetaBelowLeaf11113222
      e24KC2ThetaBelowLeaf11113223

theorem e24KC2ThetaBelowNode1111323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHL (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113230 e24KC2ThetaBelowLeaf11113231 e24KC2ThetaBelowLeaf11113232
      e24KC2ThetaBelowLeaf11113233

theorem e24KC2ThetaBelowNode1111330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowNode11113300 e24KC2ThetaBelowNode11113301 e24KC2ThetaBelowNode11113302
      e24KC2ThetaBelowNode11113303

theorem e24KC2ThetaBelowNode1111331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowNode11113310 e24KC2ThetaBelowNode11113311 e24KC2ThetaBelowNode11113312
      e24KC2ThetaBelowNode11113313

theorem e24KC2ThetaBelowNode1111332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHH (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113320 e24KC2ThetaBelowLeaf11113321 e24KC2ThetaBelowLeaf11113322
      e24KC2ThetaBelowLeaf11113323

theorem e24KC2ThetaBelowNode1111333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHH (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113330 e24KC2ThetaBelowLeaf11113331 e24KC2ThetaBelowLeaf11113332
      e24KC2ThetaBelowLeaf11113333

theorem e24KC2ThetaBelowNode100113 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH thetaBelowCell1001))
    e24KC2ThetaBelowLeaf1001130 e24KC2ThetaBelowLeaf1001131 e24KC2ThetaBelowLeaf1001132
      e24KC2ThetaBelowLeaf1001133

theorem e24KC2ThetaBelowNode100121 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL thetaBelowCell1001))
    e24KC2ThetaBelowLeaf1001210 e24KC2ThetaBelowLeaf1001211 e24KC2ThetaBelowLeaf1001212
      e24KC2ThetaBelowLeaf1001213

theorem e24KC2ThetaBelowNode100130 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH thetaBelowCell1001))
    e24KC2ThetaBelowLeaf1001300 e24KC2ThetaBelowLeaf1001301 e24KC2ThetaBelowLeaf1001302
      e24KC2ThetaBelowLeaf1001303

theorem e24KC2ThetaBelowNode100131 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH thetaBelowCell1001))
    e24KC2ThetaBelowLeaf1001310 e24KC2ThetaBelowLeaf1001311 e24KC2ThetaBelowLeaf1001312
      e24KC2ThetaBelowLeaf1001313

theorem e24KC2ThetaBelowNode101001 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLL thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010010 e24KC2ThetaBelowLeaf1010011 e24KC2ThetaBelowLeaf1010012
      e24KC2ThetaBelowLeaf1010013

theorem e24KC2ThetaBelowNode101002 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010020 e24KC2ThetaBelowLeaf1010021 e24KC2ThetaBelowLeaf1010022
      e24KC2ThetaBelowLeaf1010023

theorem e24KC2ThetaBelowNode101003 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010030 e24KC2ThetaBelowLeaf1010031 e24KC2ThetaBelowLeaf1010032
      e24KC2ThetaBelowLeaf1010033

theorem e24KC2ThetaBelowNode101010 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010100 e24KC2ThetaBelowLeaf1010101 e24KC2ThetaBelowLeaf1010102
      e24KC2ThetaBelowLeaf1010103

theorem e24KC2ThetaBelowNode101011 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010110 e24KC2ThetaBelowLeaf1010111 e24KC2ThetaBelowLeaf1010112
      e24KC2ThetaBelowLeaf1010113

theorem e24KC2ThetaBelowNode101012 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010120 e24KC2ThetaBelowLeaf1010121 e24KC2ThetaBelowLeaf1010122
      e24KC2ThetaBelowLeaf1010123

theorem e24KC2ThetaBelowNode101013 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010130 e24KC2ThetaBelowLeaf1010131 e24KC2ThetaBelowLeaf1010132
      e24KC2ThetaBelowLeaf1010133

theorem e24KC2ThetaBelowNode101020 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010200 e24KC2ThetaBelowLeaf1010201 e24KC2ThetaBelowLeaf1010202
      e24KC2ThetaBelowLeaf1010203

theorem e24KC2ThetaBelowNode101021 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010210 e24KC2ThetaBelowLeaf1010211 e24KC2ThetaBelowLeaf1010212
      e24KC2ThetaBelowLeaf1010213

theorem e24KC2ThetaBelowNode101030 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010300 e24KC2ThetaBelowLeaf1010301 e24KC2ThetaBelowLeaf1010302
      e24KC2ThetaBelowLeaf1010303

theorem e24KC2ThetaBelowNode101031 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010310 e24KC2ThetaBelowLeaf1010311 e24KC2ThetaBelowLeaf1010312
      e24KC2ThetaBelowLeaf1010313

theorem e24KC2ThetaBelowNode101032 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010320 e24KC2ThetaBelowLeaf1010321 e24KC2ThetaBelowLeaf1010322
      e24KC2ThetaBelowLeaf1010323

theorem e24KC2ThetaBelowNode101033 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010330 e24KC2ThetaBelowLeaf1010331 e24KC2ThetaBelowLeaf1010332
      e24KC2ThetaBelowLeaf1010333

theorem e24KC2ThetaBelowNode101100 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLL thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011000 e24KC2ThetaBelowLeaf1011001 e24KC2ThetaBelowLeaf1011002
      e24KC2ThetaBelowLeaf1011003

theorem e24KC2ThetaBelowNode101102 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011020 e24KC2ThetaBelowLeaf1011021 e24KC2ThetaBelowLeaf1011022
      e24KC2ThetaBelowLeaf1011023

theorem e24KC2ThetaBelowNode101103 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011030 e24KC2ThetaBelowLeaf1011031 e24KC2ThetaBelowLeaf1011032
      e24KC2ThetaBelowLeaf1011033

theorem e24KC2ThetaBelowNode101112 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011120 e24KC2ThetaBelowLeaf1011121 e24KC2ThetaBelowLeaf1011122
      e24KC2ThetaBelowLeaf1011123

theorem e24KC2ThetaBelowNode101113 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011130 e24KC2ThetaBelowLeaf1011131 e24KC2ThetaBelowLeaf1011132
      e24KC2ThetaBelowLeaf1011133

theorem e24KC2ThetaBelowNode101120 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011200 e24KC2ThetaBelowLeaf1011201 e24KC2ThetaBelowLeaf1011202
      e24KC2ThetaBelowLeaf1011203

theorem e24KC2ThetaBelowNode101121 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011210 e24KC2ThetaBelowLeaf1011211 e24KC2ThetaBelowLeaf1011212
      e24KC2ThetaBelowLeaf1011213

theorem e24KC2ThetaBelowNode101122 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011220 e24KC2ThetaBelowLeaf1011221 e24KC2ThetaBelowLeaf1011222
      e24KC2ThetaBelowLeaf1011223

theorem e24KC2ThetaBelowNode101123 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011230 e24KC2ThetaBelowLeaf1011231 e24KC2ThetaBelowLeaf1011232
      e24KC2ThetaBelowLeaf1011233

theorem e24KC2ThetaBelowNode101130 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011300 e24KC2ThetaBelowLeaf1011301 e24KC2ThetaBelowLeaf1011302
      e24KC2ThetaBelowNode1011303

theorem e24KC2ThetaBelowNode101131 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011310 e24KC2ThetaBelowNode1011311 e24KC2ThetaBelowNode1011312
      e24KC2ThetaBelowNode1011313

theorem e24KC2ThetaBelowNode101132 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011320 e24KC2ThetaBelowLeaf1011321 e24KC2ThetaBelowLeaf1011322
      e24KC2ThetaBelowLeaf1011323

theorem e24KC2ThetaBelowNode101133 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011330 e24KC2ThetaBelowLeaf1011331 e24KC2ThetaBelowLeaf1011332
      e24KC2ThetaBelowLeaf1011333

theorem e24KC2ThetaBelowNode110002 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL thetaBelowCell1100))
    e24KC2ThetaBelowLeaf1100020 e24KC2ThetaBelowLeaf1100021 e24KC2ThetaBelowLeaf1100022
      e24KC2ThetaBelowLeaf1100023

theorem e24KC2ThetaBelowNode110003 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL thetaBelowCell1100))
    e24KC2ThetaBelowLeaf1100030 e24KC2ThetaBelowLeaf1100031 e24KC2ThetaBelowNode1100032
      e24KC2ThetaBelowNode1100033

theorem e24KC2ThetaBelowNode110012 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH thetaBelowCell1100))
    e24KC2ThetaBelowLeaf1100120 e24KC2ThetaBelowLeaf1100121 e24KC2ThetaBelowNode1100122
      e24KC2ThetaBelowNode1100123

theorem e24KC2ThetaBelowNode110013 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH thetaBelowCell1100))
    e24KC2ThetaBelowLeaf1100130 e24KC2ThetaBelowLeaf1100131 e24KC2ThetaBelowNode1100132
      e24KC2ThetaBelowNode1100133

theorem e24KC2ThetaBelowNode110020 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL thetaBelowCell1100))
    e24KC2ThetaBelowNode1100200 e24KC2ThetaBelowNode1100201 e24KC2ThetaBelowNode1100202
      e24KC2ThetaBelowNode1100203

theorem e24KC2ThetaBelowNode110021 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL thetaBelowCell1100))
    e24KC2ThetaBelowNode1100210 e24KC2ThetaBelowNode1100211 e24KC2ThetaBelowNode1100212
      e24KC2ThetaBelowNode1100213

theorem e24KC2ThetaBelowNode110022 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL thetaBelowCell1100))
    e24KC2ThetaBelowLeaf1100220 e24KC2ThetaBelowLeaf1100221 e24KC2ThetaBelowLeaf1100222
      e24KC2ThetaBelowLeaf1100223

theorem e24KC2ThetaBelowNode110023 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL thetaBelowCell1100))
    e24KC2ThetaBelowLeaf1100230 e24KC2ThetaBelowLeaf1100231 e24KC2ThetaBelowLeaf1100232
      e24KC2ThetaBelowLeaf1100233

theorem e24KC2ThetaBelowNode110030 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH thetaBelowCell1100))
    e24KC2ThetaBelowNode1100300 e24KC2ThetaBelowNode1100301 e24KC2ThetaBelowNode1100302
      e24KC2ThetaBelowNode1100303

theorem e24KC2ThetaBelowNode110031 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH thetaBelowCell1100))
    e24KC2ThetaBelowNode1100310 e24KC2ThetaBelowNode1100311 e24KC2ThetaBelowNode1100312
      e24KC2ThetaBelowNode1100313

theorem e24KC2ThetaBelowNode110032 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH thetaBelowCell1100))
    e24KC2ThetaBelowLeaf1100320 e24KC2ThetaBelowLeaf1100321 e24KC2ThetaBelowLeaf1100322
      e24KC2ThetaBelowLeaf1100323

theorem e24KC2ThetaBelowNode110033 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH thetaBelowCell1100))
    e24KC2ThetaBelowNode1100330 e24KC2ThetaBelowNode1100331 e24KC2ThetaBelowLeaf1100332
      e24KC2ThetaBelowLeaf1100333

theorem e24KC2ThetaBelowNode110102 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL thetaBelowCell1101))
    e24KC2ThetaBelowLeaf1101020 e24KC2ThetaBelowLeaf1101021 e24KC2ThetaBelowNode1101022
      e24KC2ThetaBelowNode1101023

theorem e24KC2ThetaBelowNode110103 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL thetaBelowCell1101))
    e24KC2ThetaBelowLeaf1101030 e24KC2ThetaBelowLeaf1101031 e24KC2ThetaBelowLeaf1101032
      e24KC2ThetaBelowLeaf1101033

theorem e24KC2ThetaBelowNode110112 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH thetaBelowCell1101))
    e24KC2ThetaBelowLeaf1101120 e24KC2ThetaBelowLeaf1101121 e24KC2ThetaBelowLeaf1101122
      e24KC2ThetaBelowLeaf1101123

theorem e24KC2ThetaBelowNode110113 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH thetaBelowCell1101))
    e24KC2ThetaBelowLeaf1101130 e24KC2ThetaBelowLeaf1101131 e24KC2ThetaBelowLeaf1101132
      e24KC2ThetaBelowLeaf1101133

theorem e24KC2ThetaBelowNode110120 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL thetaBelowCell1101))
    e24KC2ThetaBelowNode1101200 e24KC2ThetaBelowNode1101201 e24KC2ThetaBelowNode1101202
      e24KC2ThetaBelowNode1101203

theorem e24KC2ThetaBelowNode110121 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL thetaBelowCell1101))
    e24KC2ThetaBelowNode1101210 e24KC2ThetaBelowNode1101211 e24KC2ThetaBelowNode1101212
      e24KC2ThetaBelowNode1101213

theorem e24KC2ThetaBelowNode110122 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL thetaBelowCell1101))
    e24KC2ThetaBelowNode1101220 e24KC2ThetaBelowNode1101221 e24KC2ThetaBelowLeaf1101222
      e24KC2ThetaBelowLeaf1101223

theorem e24KC2ThetaBelowNode110123 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL thetaBelowCell1101))
    e24KC2ThetaBelowNode1101230 e24KC2ThetaBelowNode1101231 e24KC2ThetaBelowLeaf1101232
      e24KC2ThetaBelowLeaf1101233

theorem e24KC2ThetaBelowNode110130 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH thetaBelowCell1101))
    e24KC2ThetaBelowNode1101300 e24KC2ThetaBelowNode1101301 e24KC2ThetaBelowNode1101302
      e24KC2ThetaBelowNode1101303

theorem e24KC2ThetaBelowNode110131 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH thetaBelowCell1101))
    e24KC2ThetaBelowNode1101310 e24KC2ThetaBelowNode1101311 e24KC2ThetaBelowNode1101312
      e24KC2ThetaBelowNode1101313

theorem e24KC2ThetaBelowNode110132 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH thetaBelowCell1101))
    e24KC2ThetaBelowNode1101320 e24KC2ThetaBelowNode1101321 e24KC2ThetaBelowLeaf1101322
      e24KC2ThetaBelowLeaf1101323

theorem e24KC2ThetaBelowNode110133 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH thetaBelowCell1101))
    e24KC2ThetaBelowNode1101330 e24KC2ThetaBelowNode1101331 e24KC2ThetaBelowLeaf1101332
      e24KC2ThetaBelowLeaf1101333

theorem e24KC2ThetaBelowNode111002 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL thetaBelowCell1110))
    e24KC2ThetaBelowLeaf1110020 e24KC2ThetaBelowLeaf1110021 e24KC2ThetaBelowLeaf1110022
      e24KC2ThetaBelowLeaf1110023

theorem e24KC2ThetaBelowNode111003 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL thetaBelowCell1110))
    e24KC2ThetaBelowLeaf1110030 e24KC2ThetaBelowLeaf1110031 e24KC2ThetaBelowLeaf1110032
      e24KC2ThetaBelowLeaf1110033

theorem e24KC2ThetaBelowNode111012 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH thetaBelowCell1110))
    e24KC2ThetaBelowLeaf1110120 e24KC2ThetaBelowLeaf1110121 e24KC2ThetaBelowLeaf1110122
      e24KC2ThetaBelowLeaf1110123

theorem e24KC2ThetaBelowNode111013 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH thetaBelowCell1110))
    e24KC2ThetaBelowLeaf1110130 e24KC2ThetaBelowLeaf1110131 e24KC2ThetaBelowLeaf1110132
      e24KC2ThetaBelowLeaf1110133

theorem e24KC2ThetaBelowNode111020 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL thetaBelowCell1110))
    e24KC2ThetaBelowNode1110200 e24KC2ThetaBelowNode1110201 e24KC2ThetaBelowNode1110202
      e24KC2ThetaBelowNode1110203

theorem e24KC2ThetaBelowNode111021 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL thetaBelowCell1110))
    e24KC2ThetaBelowNode1110210 e24KC2ThetaBelowNode1110211 e24KC2ThetaBelowNode1110212
      e24KC2ThetaBelowNode1110213

theorem e24KC2ThetaBelowNode111022 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL thetaBelowCell1110))
    e24KC2ThetaBelowNode1110220 e24KC2ThetaBelowNode1110221 e24KC2ThetaBelowLeaf1110222
      e24KC2ThetaBelowLeaf1110223

theorem e24KC2ThetaBelowNode111023 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL thetaBelowCell1110))
    e24KC2ThetaBelowNode1110230 e24KC2ThetaBelowNode1110231 e24KC2ThetaBelowLeaf1110232
      e24KC2ThetaBelowLeaf1110233

theorem e24KC2ThetaBelowNode111030 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH thetaBelowCell1110))
    e24KC2ThetaBelowNode1110300 e24KC2ThetaBelowNode1110301 e24KC2ThetaBelowNode1110302
      e24KC2ThetaBelowNode1110303

theorem e24KC2ThetaBelowNode111031 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH thetaBelowCell1110))
    e24KC2ThetaBelowNode1110310 e24KC2ThetaBelowNode1110311 e24KC2ThetaBelowNode1110312
      e24KC2ThetaBelowNode1110313

theorem e24KC2ThetaBelowNode111032 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH thetaBelowCell1110))
    e24KC2ThetaBelowNode1110320 e24KC2ThetaBelowNode1110321 e24KC2ThetaBelowLeaf1110322
      e24KC2ThetaBelowLeaf1110323

theorem e24KC2ThetaBelowNode111033 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH thetaBelowCell1110))
    e24KC2ThetaBelowNode1110330 e24KC2ThetaBelowNode1110331 e24KC2ThetaBelowLeaf1110332
      e24KC2ThetaBelowLeaf1110333

theorem e24KC2ThetaBelowNode111102 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL thetaBelowCell1111))
    e24KC2ThetaBelowLeaf1111020 e24KC2ThetaBelowLeaf1111021 e24KC2ThetaBelowLeaf1111022
      e24KC2ThetaBelowLeaf1111023

theorem e24KC2ThetaBelowNode111103 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL thetaBelowCell1111))
    e24KC2ThetaBelowLeaf1111030 e24KC2ThetaBelowLeaf1111031 e24KC2ThetaBelowLeaf1111032
      e24KC2ThetaBelowLeaf1111033

theorem e24KC2ThetaBelowNode111112 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH thetaBelowCell1111))
    e24KC2ThetaBelowLeaf1111120 e24KC2ThetaBelowLeaf1111121 e24KC2ThetaBelowLeaf1111122
      e24KC2ThetaBelowLeaf1111123

theorem e24KC2ThetaBelowNode111120 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL thetaBelowCell1111))
    e24KC2ThetaBelowNode1111200 e24KC2ThetaBelowNode1111201 e24KC2ThetaBelowNode1111202
      e24KC2ThetaBelowNode1111203

theorem e24KC2ThetaBelowNode111121 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL thetaBelowCell1111))
    e24KC2ThetaBelowNode1111210 e24KC2ThetaBelowNode1111211 e24KC2ThetaBelowNode1111212
      e24KC2ThetaBelowNode1111213

theorem e24KC2ThetaBelowNode111122 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL thetaBelowCell1111))
    e24KC2ThetaBelowNode1111220 e24KC2ThetaBelowNode1111221 e24KC2ThetaBelowNode1111222
      e24KC2ThetaBelowNode1111223

theorem e24KC2ThetaBelowNode111123 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL thetaBelowCell1111))
    e24KC2ThetaBelowNode1111230 e24KC2ThetaBelowNode1111231 e24KC2ThetaBelowNode1111232
      e24KC2ThetaBelowNode1111233

theorem e24KC2ThetaBelowNode111130 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH thetaBelowCell1111))
    e24KC2ThetaBelowLeaf1111300 e24KC2ThetaBelowLeaf1111301 e24KC2ThetaBelowNode1111302
      e24KC2ThetaBelowNode1111303

theorem e24KC2ThetaBelowNode111131 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH thetaBelowCell1111))
    e24KC2ThetaBelowLeaf1111310 e24KC2ThetaBelowLeaf1111311 e24KC2ThetaBelowNode1111312
      e24KC2ThetaBelowNode1111313

theorem e24KC2ThetaBelowNode111132 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH thetaBelowCell1111))
    e24KC2ThetaBelowNode1111320 e24KC2ThetaBelowNode1111321 e24KC2ThetaBelowNode1111322
      e24KC2ThetaBelowNode1111323

theorem e24KC2ThetaBelowNode111133 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH thetaBelowCell1111))
    e24KC2ThetaBelowNode1111330 e24KC2ThetaBelowNode1111331 e24KC2ThetaBelowNode1111332
      e24KC2ThetaBelowNode1111333

theorem e24KC2ThetaBelowNode111210 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1112)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLH thetaBelowCell1112))
    e24KC2ThetaBelowLeaf1112100 e24KC2ThetaBelowLeaf1112101 e24KC2ThetaBelowLeaf1112102
      e24KC2ThetaBelowLeaf1112103

theorem e24KC2ThetaBelowNode111211 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1112)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLH thetaBelowCell1112))
    e24KC2ThetaBelowLeaf1112110 e24KC2ThetaBelowLeaf1112111 e24KC2ThetaBelowLeaf1112112
      e24KC2ThetaBelowLeaf1112113

theorem e24KC2ThetaBelowNode111300 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1113)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLL thetaBelowCell1113))
    e24KC2ThetaBelowLeaf1113000 e24KC2ThetaBelowLeaf1113001 e24KC2ThetaBelowLeaf1113002
      e24KC2ThetaBelowLeaf1113003

theorem e24KC2ThetaBelowNode111301 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1113)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLL thetaBelowCell1113))
    e24KC2ThetaBelowLeaf1113010 e24KC2ThetaBelowLeaf1113011 e24KC2ThetaBelowLeaf1113012
      e24KC2ThetaBelowLeaf1113013

theorem e24KC2ThetaBelowNode111310 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1113)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLH thetaBelowCell1113))
    e24KC2ThetaBelowLeaf1113100 e24KC2ThetaBelowLeaf1113101 e24KC2ThetaBelowLeaf1113102
      e24KC2ThetaBelowLeaf1113103

theorem e24KC2ThetaBelowNode111311 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1113)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLH thetaBelowCell1113))
    e24KC2ThetaBelowLeaf1113110 e24KC2ThetaBelowLeaf1113111 e24KC2ThetaBelowLeaf1113112
      e24KC2ThetaBelowLeaf1113113

theorem e24KC2ThetaBelowNode01013 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0101) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell0101)
    e24KC2ThetaBelowLeaf010130 e24KC2ThetaBelowLeaf010131 e24KC2ThetaBelowLeaf010132
      e24KC2ThetaBelowLeaf010133

theorem e24KC2ThetaBelowNode01101 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0110) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell0110)
    e24KC2ThetaBelowLeaf011010 e24KC2ThetaBelowLeaf011011 e24KC2ThetaBelowLeaf011012
      e24KC2ThetaBelowLeaf011013

theorem e24KC2ThetaBelowNode01102 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0110) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell0110)
    e24KC2ThetaBelowLeaf011020 e24KC2ThetaBelowLeaf011021 e24KC2ThetaBelowLeaf011022
      e24KC2ThetaBelowLeaf011023

theorem e24KC2ThetaBelowNode01103 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0110) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell0110)
    e24KC2ThetaBelowLeaf011030 e24KC2ThetaBelowLeaf011031 e24KC2ThetaBelowLeaf011032
      e24KC2ThetaBelowLeaf011033

theorem e24KC2ThetaBelowNode01110 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell0111)
    e24KC2ThetaBelowLeaf011100 e24KC2ThetaBelowLeaf011101 e24KC2ThetaBelowLeaf011102
      e24KC2ThetaBelowLeaf011103

theorem e24KC2ThetaBelowNode01111 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell0111)
    e24KC2ThetaBelowLeaf011110 e24KC2ThetaBelowLeaf011111 e24KC2ThetaBelowLeaf011112
      e24KC2ThetaBelowLeaf011113

theorem e24KC2ThetaBelowNode01112 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell0111)
    e24KC2ThetaBelowLeaf011120 e24KC2ThetaBelowLeaf011121 e24KC2ThetaBelowLeaf011122
      e24KC2ThetaBelowLeaf011123

theorem e24KC2ThetaBelowNode01113 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell0111)
    e24KC2ThetaBelowLeaf011130 e24KC2ThetaBelowLeaf011131 e24KC2ThetaBelowLeaf011132
      e24KC2ThetaBelowLeaf011133

theorem e24KC2ThetaBelowNode10000 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1000)
    e24KC2ThetaBelowLeaf100000 e24KC2ThetaBelowLeaf100001 e24KC2ThetaBelowLeaf100002
      e24KC2ThetaBelowLeaf100003

theorem e24KC2ThetaBelowNode10001 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1000)
    e24KC2ThetaBelowLeaf100010 e24KC2ThetaBelowLeaf100011 e24KC2ThetaBelowLeaf100012
      e24KC2ThetaBelowLeaf100013

theorem e24KC2ThetaBelowNode10002 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1000)
    e24KC2ThetaBelowLeaf100020 e24KC2ThetaBelowLeaf100021 e24KC2ThetaBelowLeaf100022
      e24KC2ThetaBelowLeaf100023

theorem e24KC2ThetaBelowNode10003 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1000)
    e24KC2ThetaBelowLeaf100030 e24KC2ThetaBelowLeaf100031 e24KC2ThetaBelowLeaf100032
      e24KC2ThetaBelowLeaf100033

theorem e24KC2ThetaBelowNode10010 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1001)
    e24KC2ThetaBelowLeaf100100 e24KC2ThetaBelowLeaf100101 e24KC2ThetaBelowLeaf100102
      e24KC2ThetaBelowLeaf100103

theorem e24KC2ThetaBelowNode10011 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1001)
    e24KC2ThetaBelowLeaf100110 e24KC2ThetaBelowLeaf100111 e24KC2ThetaBelowLeaf100112
      e24KC2ThetaBelowNode100113

theorem e24KC2ThetaBelowNode10012 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1001)
    e24KC2ThetaBelowLeaf100120 e24KC2ThetaBelowNode100121 e24KC2ThetaBelowLeaf100122
      e24KC2ThetaBelowLeaf100123

theorem e24KC2ThetaBelowNode10013 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1001)
    e24KC2ThetaBelowNode100130 e24KC2ThetaBelowNode100131 e24KC2ThetaBelowLeaf100132
      e24KC2ThetaBelowLeaf100133

theorem e24KC2ThetaBelowNode10031 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1003) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1003)
    e24KC2ThetaBelowLeaf100310 e24KC2ThetaBelowLeaf100311 e24KC2ThetaBelowLeaf100312
      e24KC2ThetaBelowLeaf100313

theorem e24KC2ThetaBelowNode10100 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1010)
    e24KC2ThetaBelowLeaf101000 e24KC2ThetaBelowNode101001 e24KC2ThetaBelowNode101002
      e24KC2ThetaBelowNode101003

theorem e24KC2ThetaBelowNode10101 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1010)
    e24KC2ThetaBelowNode101010 e24KC2ThetaBelowNode101011 e24KC2ThetaBelowNode101012
      e24KC2ThetaBelowNode101013

theorem e24KC2ThetaBelowNode10102 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1010)
    e24KC2ThetaBelowNode101020 e24KC2ThetaBelowNode101021 e24KC2ThetaBelowLeaf101022
      e24KC2ThetaBelowLeaf101023

theorem e24KC2ThetaBelowNode10103 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1010)
    e24KC2ThetaBelowNode101030 e24KC2ThetaBelowNode101031 e24KC2ThetaBelowNode101032
      e24KC2ThetaBelowNode101033

theorem e24KC2ThetaBelowNode10110 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1011)
    e24KC2ThetaBelowNode101100 e24KC2ThetaBelowLeaf101101 e24KC2ThetaBelowNode101102
      e24KC2ThetaBelowNode101103

theorem e24KC2ThetaBelowNode10111 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1011)
    e24KC2ThetaBelowLeaf101110 e24KC2ThetaBelowLeaf101111 e24KC2ThetaBelowNode101112
      e24KC2ThetaBelowNode101113

theorem e24KC2ThetaBelowNode10112 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1011)
    e24KC2ThetaBelowNode101120 e24KC2ThetaBelowNode101121 e24KC2ThetaBelowNode101122
      e24KC2ThetaBelowNode101123

theorem e24KC2ThetaBelowNode10113 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1011)
    e24KC2ThetaBelowNode101130 e24KC2ThetaBelowNode101131 e24KC2ThetaBelowNode101132
      e24KC2ThetaBelowNode101133

theorem e24KC2ThetaBelowNode10120 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1012) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1012)
    e24KC2ThetaBelowLeaf101200 e24KC2ThetaBelowLeaf101201 e24KC2ThetaBelowLeaf101202
      e24KC2ThetaBelowLeaf101203

theorem e24KC2ThetaBelowNode10121 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1012) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1012)
    e24KC2ThetaBelowLeaf101210 e24KC2ThetaBelowLeaf101211 e24KC2ThetaBelowLeaf101212
      e24KC2ThetaBelowLeaf101213

theorem e24KC2ThetaBelowNode10130 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1013) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1013)
    e24KC2ThetaBelowLeaf101300 e24KC2ThetaBelowLeaf101301 e24KC2ThetaBelowLeaf101302
      e24KC2ThetaBelowLeaf101303

theorem e24KC2ThetaBelowNode10131 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1013) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1013)
    e24KC2ThetaBelowLeaf101310 e24KC2ThetaBelowLeaf101311 e24KC2ThetaBelowLeaf101312
      e24KC2ThetaBelowLeaf101313

theorem e24KC2ThetaBelowNode11000 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1100)
    e24KC2ThetaBelowLeaf110000 e24KC2ThetaBelowLeaf110001 e24KC2ThetaBelowNode110002
      e24KC2ThetaBelowNode110003

theorem e24KC2ThetaBelowNode11001 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1100)
    e24KC2ThetaBelowLeaf110010 e24KC2ThetaBelowLeaf110011 e24KC2ThetaBelowNode110012
      e24KC2ThetaBelowNode110013

theorem e24KC2ThetaBelowNode11002 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1100)
    e24KC2ThetaBelowNode110020 e24KC2ThetaBelowNode110021 e24KC2ThetaBelowNode110022
      e24KC2ThetaBelowNode110023

theorem e24KC2ThetaBelowNode11003 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1100)
    e24KC2ThetaBelowNode110030 e24KC2ThetaBelowNode110031 e24KC2ThetaBelowNode110032
      e24KC2ThetaBelowNode110033

theorem e24KC2ThetaBelowNode11010 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1101)
    e24KC2ThetaBelowLeaf110100 e24KC2ThetaBelowLeaf110101 e24KC2ThetaBelowNode110102
      e24KC2ThetaBelowNode110103

theorem e24KC2ThetaBelowNode11011 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1101)
    e24KC2ThetaBelowLeaf110110 e24KC2ThetaBelowLeaf110111 e24KC2ThetaBelowNode110112
      e24KC2ThetaBelowNode110113

theorem e24KC2ThetaBelowNode11012 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1101)
    e24KC2ThetaBelowNode110120 e24KC2ThetaBelowNode110121 e24KC2ThetaBelowNode110122
      e24KC2ThetaBelowNode110123

theorem e24KC2ThetaBelowNode11013 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1101)
    e24KC2ThetaBelowNode110130 e24KC2ThetaBelowNode110131 e24KC2ThetaBelowNode110132
      e24KC2ThetaBelowNode110133

theorem e24KC2ThetaBelowNode11020 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1102) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1102)
    e24KC2ThetaBelowLeaf110200 e24KC2ThetaBelowLeaf110201 e24KC2ThetaBelowLeaf110202
      e24KC2ThetaBelowLeaf110203

theorem e24KC2ThetaBelowNode11021 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1102) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1102)
    e24KC2ThetaBelowLeaf110210 e24KC2ThetaBelowLeaf110211 e24KC2ThetaBelowLeaf110212
      e24KC2ThetaBelowLeaf110213

theorem e24KC2ThetaBelowNode11030 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1103) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1103)
    e24KC2ThetaBelowLeaf110300 e24KC2ThetaBelowLeaf110301 e24KC2ThetaBelowLeaf110302
      e24KC2ThetaBelowLeaf110303

theorem e24KC2ThetaBelowNode11031 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1103) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1103)
    e24KC2ThetaBelowLeaf110310 e24KC2ThetaBelowLeaf110311 e24KC2ThetaBelowLeaf110312
      e24KC2ThetaBelowLeaf110313

theorem e24KC2ThetaBelowNode11100 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1110)
    e24KC2ThetaBelowLeaf111000 e24KC2ThetaBelowLeaf111001 e24KC2ThetaBelowNode111002
      e24KC2ThetaBelowNode111003

theorem e24KC2ThetaBelowNode11101 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1110)
    e24KC2ThetaBelowLeaf111010 e24KC2ThetaBelowLeaf111011 e24KC2ThetaBelowNode111012
      e24KC2ThetaBelowNode111013

theorem e24KC2ThetaBelowNode11102 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1110)
    e24KC2ThetaBelowNode111020 e24KC2ThetaBelowNode111021 e24KC2ThetaBelowNode111022
      e24KC2ThetaBelowNode111023

theorem e24KC2ThetaBelowNode11103 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1110)
    e24KC2ThetaBelowNode111030 e24KC2ThetaBelowNode111031 e24KC2ThetaBelowNode111032
      e24KC2ThetaBelowNode111033

theorem e24KC2ThetaBelowNode11110 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1111)
    e24KC2ThetaBelowLeaf111100 e24KC2ThetaBelowLeaf111101 e24KC2ThetaBelowNode111102
      e24KC2ThetaBelowNode111103

theorem e24KC2ThetaBelowNode11111 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1111)
    e24KC2ThetaBelowLeaf111110 e24KC2ThetaBelowLeaf111111 e24KC2ThetaBelowNode111112
      e24KC2ThetaBelowLeaf111113

theorem e24KC2ThetaBelowNode11112 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1111)
    e24KC2ThetaBelowNode111120 e24KC2ThetaBelowNode111121 e24KC2ThetaBelowNode111122
      e24KC2ThetaBelowNode111123

theorem e24KC2ThetaBelowNode11113 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1111)
    e24KC2ThetaBelowNode111130 e24KC2ThetaBelowNode111131 e24KC2ThetaBelowNode111132
      e24KC2ThetaBelowNode111133

theorem e24KC2ThetaBelowNode11120 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1112) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1112)
    e24KC2ThetaBelowLeaf111200 e24KC2ThetaBelowLeaf111201 e24KC2ThetaBelowLeaf111202
      e24KC2ThetaBelowLeaf111203

theorem e24KC2ThetaBelowNode11121 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1112) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1112)
    e24KC2ThetaBelowNode111210 e24KC2ThetaBelowNode111211 e24KC2ThetaBelowLeaf111212
      e24KC2ThetaBelowLeaf111213

theorem e24KC2ThetaBelowNode11130 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1113) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1113)
    e24KC2ThetaBelowNode111300 e24KC2ThetaBelowNode111301 e24KC2ThetaBelowLeaf111302
      e24KC2ThetaBelowLeaf111303

theorem e24KC2ThetaBelowNode11131 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1113) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1113)
    e24KC2ThetaBelowNode111310 e24KC2ThetaBelowNode111311 e24KC2ThetaBelowLeaf111312
      e24KC2ThetaBelowLeaf111313

theorem e24KC2ThetaBelowNode0003 :
    adaptiveCoverCheck 14 thetaBelowCell0003 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0003
    e24KC2ThetaBelowLeaf00030 e24KC2ThetaBelowLeaf00031 e24KC2ThetaBelowLeaf00032
      e24KC2ThetaBelowLeaf00033

theorem e24KC2ThetaBelowNode0010 :
    adaptiveCoverCheck 14 thetaBelowCell0010 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0010
    e24KC2ThetaBelowLeaf00100 e24KC2ThetaBelowLeaf00101 e24KC2ThetaBelowLeaf00102
      e24KC2ThetaBelowLeaf00103

theorem e24KC2ThetaBelowNode0011 :
    adaptiveCoverCheck 14 thetaBelowCell0011 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0011
    e24KC2ThetaBelowLeaf00110 e24KC2ThetaBelowLeaf00111 e24KC2ThetaBelowLeaf00112
      e24KC2ThetaBelowLeaf00113

theorem e24KC2ThetaBelowNode0012 :
    adaptiveCoverCheck 14 thetaBelowCell0012 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0012
    e24KC2ThetaBelowLeaf00120 e24KC2ThetaBelowLeaf00121 e24KC2ThetaBelowLeaf00122
      e24KC2ThetaBelowLeaf00123

theorem e24KC2ThetaBelowNode0013 :
    adaptiveCoverCheck 14 thetaBelowCell0013 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0013
    e24KC2ThetaBelowLeaf00130 e24KC2ThetaBelowLeaf00131 e24KC2ThetaBelowLeaf00132
      e24KC2ThetaBelowLeaf00133

theorem e24KC2ThetaBelowNode0100 :
    adaptiveCoverCheck 14 thetaBelowCell0100 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0100
    e24KC2ThetaBelowLeaf01000 e24KC2ThetaBelowLeaf01001 e24KC2ThetaBelowLeaf01002
      e24KC2ThetaBelowLeaf01003

theorem e24KC2ThetaBelowNode0101 :
    adaptiveCoverCheck 14 thetaBelowCell0101 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0101
    e24KC2ThetaBelowLeaf01010 e24KC2ThetaBelowLeaf01011 e24KC2ThetaBelowLeaf01012
      e24KC2ThetaBelowNode01013

theorem e24KC2ThetaBelowNode0102 :
    adaptiveCoverCheck 14 thetaBelowCell0102 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0102
    e24KC2ThetaBelowLeaf01020 e24KC2ThetaBelowLeaf01021 e24KC2ThetaBelowLeaf01022
      e24KC2ThetaBelowLeaf01023

theorem e24KC2ThetaBelowNode0103 :
    adaptiveCoverCheck 14 thetaBelowCell0103 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0103
    e24KC2ThetaBelowLeaf01030 e24KC2ThetaBelowLeaf01031 e24KC2ThetaBelowLeaf01032
      e24KC2ThetaBelowLeaf01033

theorem e24KC2ThetaBelowNode0110 :
    adaptiveCoverCheck 14 thetaBelowCell0110 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0110
    e24KC2ThetaBelowLeaf01100 e24KC2ThetaBelowNode01101 e24KC2ThetaBelowNode01102
      e24KC2ThetaBelowNode01103

theorem e24KC2ThetaBelowNode0111 :
    adaptiveCoverCheck 14 thetaBelowCell0111 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0111
    e24KC2ThetaBelowNode01110 e24KC2ThetaBelowNode01111 e24KC2ThetaBelowNode01112
      e24KC2ThetaBelowNode01113

theorem e24KC2ThetaBelowNode0112 :
    adaptiveCoverCheck 14 thetaBelowCell0112 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0112
    e24KC2ThetaBelowLeaf01120 e24KC2ThetaBelowLeaf01121 e24KC2ThetaBelowLeaf01122
      e24KC2ThetaBelowLeaf01123

theorem e24KC2ThetaBelowNode0113 :
    adaptiveCoverCheck 14 thetaBelowCell0113 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0113
    e24KC2ThetaBelowLeaf01130 e24KC2ThetaBelowLeaf01131 e24KC2ThetaBelowLeaf01132
      e24KC2ThetaBelowLeaf01133

theorem e24KC2ThetaBelowNode1000 :
    adaptiveCoverCheck 14 thetaBelowCell1000 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1000
    e24KC2ThetaBelowNode10000 e24KC2ThetaBelowNode10001 e24KC2ThetaBelowNode10002
      e24KC2ThetaBelowNode10003

theorem e24KC2ThetaBelowNode1001 :
    adaptiveCoverCheck 14 thetaBelowCell1001 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1001
    e24KC2ThetaBelowNode10010 e24KC2ThetaBelowNode10011 e24KC2ThetaBelowNode10012
      e24KC2ThetaBelowNode10013

theorem e24KC2ThetaBelowNode1002 :
    adaptiveCoverCheck 14 thetaBelowCell1002 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1002
    e24KC2ThetaBelowLeaf10020 e24KC2ThetaBelowLeaf10021 e24KC2ThetaBelowLeaf10022
      e24KC2ThetaBelowLeaf10023

theorem e24KC2ThetaBelowNode1003 :
    adaptiveCoverCheck 14 thetaBelowCell1003 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1003
    e24KC2ThetaBelowLeaf10030 e24KC2ThetaBelowNode10031 e24KC2ThetaBelowLeaf10032
      e24KC2ThetaBelowLeaf10033

theorem e24KC2ThetaBelowNode1010 :
    adaptiveCoverCheck 14 thetaBelowCell1010 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1010
    e24KC2ThetaBelowNode10100 e24KC2ThetaBelowNode10101 e24KC2ThetaBelowNode10102
      e24KC2ThetaBelowNode10103

theorem e24KC2ThetaBelowNode1011 :
    adaptiveCoverCheck 14 thetaBelowCell1011 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1011
    e24KC2ThetaBelowNode10110 e24KC2ThetaBelowNode10111 e24KC2ThetaBelowNode10112
      e24KC2ThetaBelowNode10113

theorem e24KC2ThetaBelowNode1012 :
    adaptiveCoverCheck 14 thetaBelowCell1012 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1012
    e24KC2ThetaBelowNode10120 e24KC2ThetaBelowNode10121 e24KC2ThetaBelowLeaf10122
      e24KC2ThetaBelowLeaf10123

theorem e24KC2ThetaBelowNode1013 :
    adaptiveCoverCheck 14 thetaBelowCell1013 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1013
    e24KC2ThetaBelowNode10130 e24KC2ThetaBelowNode10131 e24KC2ThetaBelowLeaf10132
      e24KC2ThetaBelowLeaf10133

theorem e24KC2ThetaBelowNode1100 :
    adaptiveCoverCheck 14 thetaBelowCell1100 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1100
    e24KC2ThetaBelowNode11000 e24KC2ThetaBelowNode11001 e24KC2ThetaBelowNode11002
      e24KC2ThetaBelowNode11003

theorem e24KC2ThetaBelowNode1101 :
    adaptiveCoverCheck 14 thetaBelowCell1101 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1101
    e24KC2ThetaBelowNode11010 e24KC2ThetaBelowNode11011 e24KC2ThetaBelowNode11012
      e24KC2ThetaBelowNode11013

theorem e24KC2ThetaBelowNode1102 :
    adaptiveCoverCheck 14 thetaBelowCell1102 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1102
    e24KC2ThetaBelowNode11020 e24KC2ThetaBelowNode11021 e24KC2ThetaBelowLeaf11022
      e24KC2ThetaBelowLeaf11023

theorem e24KC2ThetaBelowNode1103 :
    adaptiveCoverCheck 14 thetaBelowCell1103 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1103
    e24KC2ThetaBelowNode11030 e24KC2ThetaBelowNode11031 e24KC2ThetaBelowLeaf11032
      e24KC2ThetaBelowLeaf11033

theorem e24KC2ThetaBelowNode1110 :
    adaptiveCoverCheck 14 thetaBelowCell1110 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1110
    e24KC2ThetaBelowNode11100 e24KC2ThetaBelowNode11101 e24KC2ThetaBelowNode11102
      e24KC2ThetaBelowNode11103

theorem e24KC2ThetaBelowNode1111 :
    adaptiveCoverCheck 14 thetaBelowCell1111 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1111
    e24KC2ThetaBelowNode11110 e24KC2ThetaBelowNode11111 e24KC2ThetaBelowNode11112
      e24KC2ThetaBelowNode11113

theorem e24KC2ThetaBelowNode1112 :
    adaptiveCoverCheck 14 thetaBelowCell1112 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1112
    e24KC2ThetaBelowNode11120 e24KC2ThetaBelowNode11121 e24KC2ThetaBelowLeaf11122
      e24KC2ThetaBelowLeaf11123

theorem e24KC2ThetaBelowNode1113 :
    adaptiveCoverCheck 14 thetaBelowCell1113 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1113
    e24KC2ThetaBelowNode11130 e24KC2ThetaBelowNode11131 e24KC2ThetaBelowLeaf11132
      e24KC2ThetaBelowLeaf11133

theorem e24KC2ThetaBelowNode1121 :
    adaptiveCoverCheck 14 thetaBelowCell1121 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1121
    e24KC2ThetaBelowLeaf11210 e24KC2ThetaBelowLeaf11211 e24KC2ThetaBelowLeaf11212
      e24KC2ThetaBelowLeaf11213

theorem e24KC2ThetaBelowNode1130 :
    adaptiveCoverCheck 14 thetaBelowCell1130 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1130
    e24KC2ThetaBelowLeaf11300 e24KC2ThetaBelowLeaf11301 e24KC2ThetaBelowLeaf11302
      e24KC2ThetaBelowLeaf11303

theorem e24KC2ThetaBelowNode1131 :
    adaptiveCoverCheck 14 thetaBelowCell1131 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1131
    e24KC2ThetaBelowLeaf11310 e24KC2ThetaBelowLeaf11311 e24KC2ThetaBelowLeaf11312
      e24KC2ThetaBelowLeaf11313

theorem e24KC2ThetaBelowNode000 :
    adaptiveCoverCheck 15 (childLL (childLL (childLL e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLL (childLL (childLL e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf0000 e24KC2ThetaBelowLeaf0001 e24KC2ThetaBelowLeaf0002
      e24KC2ThetaBelowNode0003

theorem e24KC2ThetaBelowNode001 :
    adaptiveCoverCheck 15 (childLH (childLL (childLL e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLH (childLL (childLL e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode0010 e24KC2ThetaBelowNode0011 e24KC2ThetaBelowNode0012
      e24KC2ThetaBelowNode0013

theorem e24KC2ThetaBelowNode003 :
    adaptiveCoverCheck 15 (childHH (childLL (childLL e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHH (childLL (childLL e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf0030 e24KC2ThetaBelowLeaf0031 e24KC2ThetaBelowLeaf0032
      e24KC2ThetaBelowLeaf0033

theorem e24KC2ThetaBelowNode010 :
    adaptiveCoverCheck 15 (childLL (childLH (childLL e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLL (childLH (childLL e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode0100 e24KC2ThetaBelowNode0101 e24KC2ThetaBelowNode0102
      e24KC2ThetaBelowNode0103

theorem e24KC2ThetaBelowNode011 :
    adaptiveCoverCheck 15 (childLH (childLH (childLL e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLH (childLH (childLL e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode0110 e24KC2ThetaBelowNode0111 e24KC2ThetaBelowNode0112
      e24KC2ThetaBelowNode0113

theorem e24KC2ThetaBelowNode012 :
    adaptiveCoverCheck 15 (childHL (childLH (childLL e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHL (childLH (childLL e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf0120 e24KC2ThetaBelowLeaf0121 e24KC2ThetaBelowLeaf0122
      e24KC2ThetaBelowLeaf0123

theorem e24KC2ThetaBelowNode013 :
    adaptiveCoverCheck 15 (childHH (childLH (childLL e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHH (childLH (childLL e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf0130 e24KC2ThetaBelowLeaf0131 e24KC2ThetaBelowLeaf0132
      e24KC2ThetaBelowLeaf0133

theorem e24KC2ThetaBelowNode100 :
    adaptiveCoverCheck 15 (childLL (childLL (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLL (childLL (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode1000 e24KC2ThetaBelowNode1001 e24KC2ThetaBelowNode1002
      e24KC2ThetaBelowNode1003

theorem e24KC2ThetaBelowNode101 :
    adaptiveCoverCheck 15 (childLH (childLL (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLH (childLL (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode1010 e24KC2ThetaBelowNode1011 e24KC2ThetaBelowNode1012
      e24KC2ThetaBelowNode1013

theorem e24KC2ThetaBelowNode102 :
    adaptiveCoverCheck 15 (childHL (childLL (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHL (childLL (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf1020 e24KC2ThetaBelowLeaf1021 e24KC2ThetaBelowLeaf1022
      e24KC2ThetaBelowLeaf1023

theorem e24KC2ThetaBelowNode103 :
    adaptiveCoverCheck 15 (childHH (childLL (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHH (childLL (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf1030 e24KC2ThetaBelowLeaf1031 e24KC2ThetaBelowLeaf1032
      e24KC2ThetaBelowLeaf1033

theorem e24KC2ThetaBelowNode110 :
    adaptiveCoverCheck 15 (childLL (childLH (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLL (childLH (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode1100 e24KC2ThetaBelowNode1101 e24KC2ThetaBelowNode1102
      e24KC2ThetaBelowNode1103

theorem e24KC2ThetaBelowNode111 :
    adaptiveCoverCheck 15 (childLH (childLH (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLH (childLH (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode1110 e24KC2ThetaBelowNode1111 e24KC2ThetaBelowNode1112
      e24KC2ThetaBelowNode1113

theorem e24KC2ThetaBelowNode112 :
    adaptiveCoverCheck 15 (childHL (childLH (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHL (childLH (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf1120 e24KC2ThetaBelowNode1121 e24KC2ThetaBelowLeaf1122
      e24KC2ThetaBelowLeaf1123

theorem e24KC2ThetaBelowNode113 :
    adaptiveCoverCheck 15 (childHH (childLH (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHH (childLH (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode1130 e24KC2ThetaBelowNode1131 e24KC2ThetaBelowLeaf1132
      e24KC2ThetaBelowLeaf1133

theorem e24KC2ThetaBelowNode130 :
    adaptiveCoverCheck 15 (childLL (childHH (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLL (childHH (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf1300 e24KC2ThetaBelowLeaf1301 e24KC2ThetaBelowLeaf1302
      e24KC2ThetaBelowLeaf1303

theorem e24KC2ThetaBelowNode131 :
    adaptiveCoverCheck 15 (childLH (childHH (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLH (childHH (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf1310 e24KC2ThetaBelowLeaf1311 e24KC2ThetaBelowLeaf1312
      e24KC2ThetaBelowLeaf1313

theorem e24KC2ThetaBelowNode00 :
    adaptiveCoverCheck 16 (childLL (childLL e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLL (childLL e24ThetaBelowRoot))
    e24KC2ThetaBelowNode000 e24KC2ThetaBelowNode001 e24KC2ThetaBelowLeaf002 e24KC2ThetaBelowNode003

theorem e24KC2ThetaBelowNode01 :
    adaptiveCoverCheck 16 (childLH (childLL e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLH (childLL e24ThetaBelowRoot))
    e24KC2ThetaBelowNode010 e24KC2ThetaBelowNode011 e24KC2ThetaBelowNode012 e24KC2ThetaBelowNode013

theorem e24KC2ThetaBelowNode03 :
    adaptiveCoverCheck 16 (childHH (childLL e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHH (childLL e24ThetaBelowRoot))
    e24KC2ThetaBelowLeaf030 e24KC2ThetaBelowLeaf031 e24KC2ThetaBelowLeaf032 e24KC2ThetaBelowLeaf033

theorem e24KC2ThetaBelowNode10 :
    adaptiveCoverCheck 16 (childLL (childLH e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLL (childLH e24ThetaBelowRoot))
    e24KC2ThetaBelowNode100 e24KC2ThetaBelowNode101 e24KC2ThetaBelowNode102 e24KC2ThetaBelowNode103

theorem e24KC2ThetaBelowNode11 :
    adaptiveCoverCheck 16 (childLH (childLH e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLH (childLH e24ThetaBelowRoot))
    e24KC2ThetaBelowNode110 e24KC2ThetaBelowNode111 e24KC2ThetaBelowNode112 e24KC2ThetaBelowNode113

theorem e24KC2ThetaBelowNode12 :
    adaptiveCoverCheck 16 (childHL (childLH e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHL (childLH e24ThetaBelowRoot))
    e24KC2ThetaBelowLeaf120 e24KC2ThetaBelowLeaf121 e24KC2ThetaBelowLeaf122 e24KC2ThetaBelowLeaf123

theorem e24KC2ThetaBelowNode13 :
    adaptiveCoverCheck 16 (childHH (childLH e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHH (childLH e24ThetaBelowRoot))
    e24KC2ThetaBelowNode130 e24KC2ThetaBelowNode131 e24KC2ThetaBelowLeaf132 e24KC2ThetaBelowLeaf133

theorem e24KC2ThetaBelowNode30 :
    adaptiveCoverCheck 16 (childLL (childHH e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLL (childHH e24ThetaBelowRoot))
    e24KC2ThetaBelowLeaf300 e24KC2ThetaBelowLeaf301 e24KC2ThetaBelowLeaf302 e24KC2ThetaBelowLeaf303

theorem e24KC2ThetaBelowNode31 :
    adaptiveCoverCheck 16 (childLH (childHH e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLH (childHH e24ThetaBelowRoot))
    e24KC2ThetaBelowLeaf310 e24KC2ThetaBelowLeaf311 e24KC2ThetaBelowLeaf312 e24KC2ThetaBelowLeaf313

theorem e24KC2ThetaBelowNode33 :
    adaptiveCoverCheck 16 (childHH (childHH e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHH (childHH e24ThetaBelowRoot))
    e24KC2ThetaBelowLeaf330 e24KC2ThetaBelowLeaf331 e24KC2ThetaBelowLeaf332 e24KC2ThetaBelowLeaf333

theorem e24KC2ThetaBelowNode0 :
    adaptiveCoverCheck 17 (childLL e24ThetaBelowRoot) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childLL e24ThetaBelowRoot)
    e24KC2ThetaBelowNode00 e24KC2ThetaBelowNode01 e24KC2ThetaBelowLeaf02 e24KC2ThetaBelowNode03

theorem e24KC2ThetaBelowNode1 :
    adaptiveCoverCheck 17 (childLH e24ThetaBelowRoot) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childLH e24ThetaBelowRoot)
    e24KC2ThetaBelowNode10 e24KC2ThetaBelowNode11 e24KC2ThetaBelowNode12 e24KC2ThetaBelowNode13

theorem e24KC2ThetaBelowNode3 :
    adaptiveCoverCheck 17 (childHH e24ThetaBelowRoot) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childHH e24ThetaBelowRoot)
    e24KC2ThetaBelowNode30 e24KC2ThetaBelowNode31 e24KC2ThetaBelowLeaf32 e24KC2ThetaBelowNode33

theorem e24KC2ThetaBelowNodeROOT :
    adaptiveCoverCheck 18 e24ThetaBelowRoot = true :=
  adaptiveCoverCheck_succ_of_children 17 e24ThetaBelowRoot
    e24KC2ThetaBelowNode0 e24KC2ThetaBelowNode1 e24KC2ThetaBelowLeaf2 e24KC2ThetaBelowNode3

theorem e24ThetaBelowKernelCheck :
    adaptiveCoverCheck 18 e24ThetaBelowRoot = true :=
  e24KC2ThetaBelowNodeROOT

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c0_c0_6_00029
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse9ea903ef1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse9ea903ef1

open CertificateCellse9ea903ef1

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c0 :
    adaptiveCoverCheck 6 (childLL (childLL phiAboveCell11011010)) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childLL (childLL phiAboveCell11011010))
    e24KC2PhiAboveLeaf1101101_c0_c0_c0_c0 e24KC2PhiAboveLeaf1101101_c0_c0_c0_c1
      e24KC2PhiAboveLeaf1101101_c0_c0_c0_c2 e24KC2PhiAboveLeaf1101101_c0_c0_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c0_c1_c0_5_00036
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells89d797401e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells89d797401e

open CertificateCells89d797401e

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0 :
    adaptiveCoverCheck 5 (childLL (childLH (childLL phiAboveCell11011010))) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childLH (childLL phiAboveCell11011010)))
    e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0_c0 e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0_c1
      e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0_c2 e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c0_c1_c1_5_00042
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsafdf6e4305

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsafdf6e4305

open CertificateCellsafdf6e4305

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1 :
    adaptiveCoverCheck 5 (childLH (childLH (childLL phiAboveCell11011010))) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childLH (childLL phiAboveCell11011010)))
    e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1_c0 e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1_c1
      e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1_c2 e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c0_c1_6_00045
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0d2c374949

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells0d2c374949

open CertificateCells0d2c374949

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1 :
    adaptiveCoverCheck 6 (childLH (childLL phiAboveCell11011010)) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childLH (childLL phiAboveCell11011010))
    e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0 e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1
      e24KC2PhiAboveLeaf1101101_c0_c0_c1_c2 e24KC2PhiAboveLeaf1101101_c0_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c0_7_00048
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3df86e4955

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells3df86e4955

open CertificateCells3df86e4955

theorem e24KC2PhiAboveLeaf1101101_c0_c0 :
    adaptiveCoverCheck 7 (childLL phiAboveCell11011010) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childLL phiAboveCell11011010)
    e24KC2PhiAboveLeaf1101101_c0_c0_c0 e24KC2PhiAboveLeaf1101101_c0_c0_c1
      e24KC2PhiAboveLeaf1101101_c0_c0_c2 e24KC2PhiAboveLeaf1101101_c0_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c1_c0_c0_5_00056
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3298a326ef

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells3298a326ef

open CertificateCells3298a326ef

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0 :
    adaptiveCoverCheck 5 (childLL (childLL (childLH phiAboveCell11011010))) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childLL (childLH phiAboveCell11011010)))
    e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0_c0 e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0_c1
      e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0_c2 e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c1_c0_c1_5_00062
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells47980ca575

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells47980ca575

open CertificateCells47980ca575

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1 :
    adaptiveCoverCheck 5 (childLH (childLL (childLH phiAboveCell11011010))) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childLL (childLH phiAboveCell11011010)))
    e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1_c0 e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1_c1
      e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1_c2 e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c1_c0_6_00065
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsfed39385df

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsfed39385df

open CertificateCellsfed39385df

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0 :
    adaptiveCoverCheck 6 (childLL (childLH phiAboveCell11011010)) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childLL (childLH phiAboveCell11011010))
    e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0 e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1
      e24KC2PhiAboveLeaf1101101_c0_c1_c0_c2 e24KC2PhiAboveLeaf1101101_c0_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c1_c1_6_00071
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb1b33fecca

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsb1b33fecca

open CertificateCellsb1b33fecca

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c1 :
    adaptiveCoverCheck 6 (childLH (childLH phiAboveCell11011010)) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childLH (childLH phiAboveCell11011010))
    e24KC2PhiAboveLeaf1101101_c0_c1_c1_c0 e24KC2PhiAboveLeaf1101101_c0_c1_c1_c1
      e24KC2PhiAboveLeaf1101101_c0_c1_c1_c2 e24KC2PhiAboveLeaf1101101_c0_c1_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c1_7_00074
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc427a8578f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsc427a8578f

open CertificateCellsc427a8578f

theorem e24KC2PhiAboveLeaf1101101_c0_c1 :
    adaptiveCoverCheck 7 (childLH phiAboveCell11011010) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childLH phiAboveCell11011010)
    e24KC2PhiAboveLeaf1101101_c0_c1_c0 e24KC2PhiAboveLeaf1101101_c0_c1_c1
      e24KC2PhiAboveLeaf1101101_c0_c1_c2 e24KC2PhiAboveLeaf1101101_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_8_00077
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells25978ec18d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells25978ec18d

open CertificateCells25978ec18d

theorem e24KC2PhiAboveLeaf1101101_c0 :
    adaptiveCoverCheck 8 phiAboveCell11011010 = true :=
  adaptiveCoverCheck_succ_of_children 7 phiAboveCell11011010
    e24KC2PhiAboveLeaf1101101_c0_c0 e24KC2PhiAboveLeaf1101101_c0_c1
      e24KC2PhiAboveLeaf1101101_c0_c2 e24KC2PhiAboveLeaf1101101_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c1_c0_c0_6_00085
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse6161a42be

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse6161a42be

open CertificateCellse6161a42be

theorem e24KC2PhiAboveLeaf1101101_c1_c0_c0 :
    adaptiveCoverCheck 6 (childLL (childLL phiAboveCell11011011)) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childLL (childLL phiAboveCell11011011))
    e24KC2PhiAboveLeaf1101101_c1_c0_c0_c0 e24KC2PhiAboveLeaf1101101_c1_c0_c0_c1
      e24KC2PhiAboveLeaf1101101_c1_c0_c0_c2 e24KC2PhiAboveLeaf1101101_c1_c0_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c1_c0_c1_6_00091
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1f6ffcc997

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells1f6ffcc997

open CertificateCells1f6ffcc997

theorem e24KC2PhiAboveLeaf1101101_c1_c0_c1 :
    adaptiveCoverCheck 6 (childLH (childLL phiAboveCell11011011)) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childLH (childLL phiAboveCell11011011))
    e24KC2PhiAboveLeaf1101101_c1_c0_c1_c0 e24KC2PhiAboveLeaf1101101_c1_c0_c1_c1
      e24KC2PhiAboveLeaf1101101_c1_c0_c1_c2 e24KC2PhiAboveLeaf1101101_c1_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c1_c0_7_00094
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1275d3adc4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells1275d3adc4

open CertificateCells1275d3adc4

theorem e24KC2PhiAboveLeaf1101101_c1_c0 :
    adaptiveCoverCheck 7 (childLL phiAboveCell11011011) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childLL phiAboveCell11011011)
    e24KC2PhiAboveLeaf1101101_c1_c0_c0 e24KC2PhiAboveLeaf1101101_c1_c0_c1
      e24KC2PhiAboveLeaf1101101_c1_c0_c2 e24KC2PhiAboveLeaf1101101_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c1_c1_c0_6_00101
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells021b870816

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells021b870816

open CertificateCells021b870816

theorem e24KC2PhiAboveLeaf1101101_c1_c1_c0 :
    adaptiveCoverCheck 6 (childLL (childLH phiAboveCell11011011)) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childLL (childLH phiAboveCell11011011))
    e24KC2PhiAboveLeaf1101101_c1_c1_c0_c0 e24KC2PhiAboveLeaf1101101_c1_c1_c0_c1
      e24KC2PhiAboveLeaf1101101_c1_c1_c0_c2 e24KC2PhiAboveLeaf1101101_c1_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c1_c1_7_00105
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9ade3f586f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells9ade3f586f

open CertificateCells9ade3f586f

theorem e24KC2PhiAboveLeaf1101101_c1_c1 :
    adaptiveCoverCheck 7 (childLH phiAboveCell11011011) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childLH phiAboveCell11011011)
    e24KC2PhiAboveLeaf1101101_c1_c1_c0 e24KC2PhiAboveLeaf1101101_c1_c1_c1
      e24KC2PhiAboveLeaf1101101_c1_c1_c2 e24KC2PhiAboveLeaf1101101_c1_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c1_8_00108
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsfd8221930a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsfd8221930a

open CertificateCellsfd8221930a

theorem e24KC2PhiAboveLeaf1101101_c1 :
    adaptiveCoverCheck 8 phiAboveCell11011011 = true :=
  adaptiveCoverCheck_succ_of_children 7 phiAboveCell11011011
    e24KC2PhiAboveLeaf1101101_c1_c0 e24KC2PhiAboveLeaf1101101_c1_c1
      e24KC2PhiAboveLeaf1101101_c1_c2 e24KC2PhiAboveLeaf1101101_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_9_00111
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5aaf24f73d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells5aaf24f73d

open CertificateCells5aaf24f73d

theorem e24KC2PhiAboveLeaf1101101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH phiAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childLH phiAboveCell1101)))
    e24KC2PhiAboveLeaf1101101_c0 e24KC2PhiAboveLeaf1101101_c1 e24KC2PhiAboveLeaf1101101_c2
      e24KC2PhiAboveLeaf1101101_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101110_c0_c0_7_00122
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells31cca9f2c5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells31cca9f2c5

open CertificateCells31cca9f2c5

theorem e24KC2PhiAboveLeaf1101110_c0_c0 :
    adaptiveCoverCheck 7 (childLL phiAboveCell11011100) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childLL phiAboveCell11011100)
    e24KC2PhiAboveLeaf1101110_c0_c0_c0 e24KC2PhiAboveLeaf1101110_c0_c0_c1
      e24KC2PhiAboveLeaf1101110_c0_c0_c2 e24KC2PhiAboveLeaf1101110_c0_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101110_c0_c1_c0_6_00129
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0a8495a296

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells0a8495a296

open CertificateCells0a8495a296

theorem e24KC2PhiAboveLeaf1101110_c0_c1_c0 :
    adaptiveCoverCheck 6 (childLL (childLH phiAboveCell11011100)) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childLL (childLH phiAboveCell11011100))
    e24KC2PhiAboveLeaf1101110_c0_c1_c0_c0 e24KC2PhiAboveLeaf1101110_c0_c1_c0_c1
      e24KC2PhiAboveLeaf1101110_c0_c1_c0_c2 e24KC2PhiAboveLeaf1101110_c0_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101110_c0_c1_7_00133
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4cabb07dbd

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells4cabb07dbd

open CertificateCells4cabb07dbd

theorem e24KC2PhiAboveLeaf1101110_c0_c1 :
    adaptiveCoverCheck 7 (childLH phiAboveCell11011100) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childLH phiAboveCell11011100)
    e24KC2PhiAboveLeaf1101110_c0_c1_c0 e24KC2PhiAboveLeaf1101110_c0_c1_c1
      e24KC2PhiAboveLeaf1101110_c0_c1_c2 e24KC2PhiAboveLeaf1101110_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101110_c0_8_00136
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc6c93e8f5c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsc6c93e8f5c

open CertificateCellsc6c93e8f5c

theorem e24KC2PhiAboveLeaf1101110_c0 :
    adaptiveCoverCheck 8 phiAboveCell11011100 = true :=
  adaptiveCoverCheck_succ_of_children 7 phiAboveCell11011100
    e24KC2PhiAboveLeaf1101110_c0_c0 e24KC2PhiAboveLeaf1101110_c0_c1
      e24KC2PhiAboveLeaf1101110_c0_c2 e24KC2PhiAboveLeaf1101110_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101110_c1_8_00142
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsaa40da30f6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsaa40da30f6

open CertificateCellsaa40da30f6

theorem e24KC2PhiAboveLeaf1101110_c1 :
    adaptiveCoverCheck 8 phiAboveCell11011101 = true :=
  adaptiveCoverCheck_succ_of_children 7 phiAboveCell11011101
    e24KC2PhiAboveLeaf1101110_c1_c0 e24KC2PhiAboveLeaf1101110_c1_c1
      e24KC2PhiAboveLeaf1101110_c1_c2 e24KC2PhiAboveLeaf1101110_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101110_9_00145
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells919c5d7ca9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells919c5d7ca9

open CertificateCells919c5d7ca9

theorem e24KC2PhiAboveLeaf1101110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH phiAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childLH phiAboveCell1101)))
    e24KC2PhiAboveLeaf1101110_c0 e24KC2PhiAboveLeaf1101110_c1 e24KC2PhiAboveLeaf1101110_c2
      e24KC2PhiAboveLeaf1101110_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101111_c0_c1_7_00156
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells87d4f5e678

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells87d4f5e678

open CertificateCells87d4f5e678

theorem e24KC2PhiAboveLeaf1101111_c0_c1 :
    adaptiveCoverCheck 7 (childLH phiAboveCell11011110) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childLH phiAboveCell11011110)
    e24KC2PhiAboveLeaf1101111_c0_c1_c0 e24KC2PhiAboveLeaf1101111_c0_c1_c1
      e24KC2PhiAboveLeaf1101111_c0_c1_c2 e24KC2PhiAboveLeaf1101111_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101111_c0_8_00159
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsefc5f924ee

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsefc5f924ee

open CertificateCellsefc5f924ee

theorem e24KC2PhiAboveLeaf1101111_c0 :
    adaptiveCoverCheck 8 phiAboveCell11011110 = true :=
  adaptiveCoverCheck_succ_of_children 7 phiAboveCell11011110
    e24KC2PhiAboveLeaf1101111_c0_c0 e24KC2PhiAboveLeaf1101111_c0_c1
      e24KC2PhiAboveLeaf1101111_c0_c2 e24KC2PhiAboveLeaf1101111_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101111_c1_8_00165
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsac583a159d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsac583a159d

open CertificateCellsac583a159d

theorem e24KC2PhiAboveLeaf1101111_c1 :
    adaptiveCoverCheck 8 phiAboveCell11011111 = true :=
  adaptiveCoverCheck_succ_of_children 7 phiAboveCell11011111
    e24KC2PhiAboveLeaf1101111_c1_c0 e24KC2PhiAboveLeaf1101111_c1_c1
      e24KC2PhiAboveLeaf1101111_c1_c2 e24KC2PhiAboveLeaf1101111_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101111_9_00168
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf317a94cb3

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsf317a94cb3

open CertificateCellsf317a94cb3

theorem e24KC2PhiAboveLeaf1101111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH phiAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childLH phiAboveCell1101)))
    e24KC2PhiAboveLeaf1101111_c0 e24KC2PhiAboveLeaf1101111_c1 e24KC2PhiAboveLeaf1101111_c2
      e24KC2PhiAboveLeaf1101111_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1110000_c0_8_00178
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf7dce840c8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsf7dce840c8

open CertificateCellsf7dce840c8

theorem e24KC2PhiAboveLeaf1110000_c0 :
    adaptiveCoverCheck 8 phiAboveCell11100000 = true :=
  adaptiveCoverCheck_succ_of_children 7 phiAboveCell11100000
    e24KC2PhiAboveLeaf1110000_c0_c0 e24KC2PhiAboveLeaf1110000_c0_c1
      e24KC2PhiAboveLeaf1110000_c0_c2 e24KC2PhiAboveLeaf1110000_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1110000_9_00182
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5fe660c4fc

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells5fe660c4fc

open CertificateCells5fe660c4fc

theorem e24KC2PhiAboveLeaf1110000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL phiAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childLL phiAboveCell1110)))
    e24KC2PhiAboveLeaf1110000_c0 e24KC2PhiAboveLeaf1110000_c1 e24KC2PhiAboveLeaf1110000_c2
      e24KC2PhiAboveLeaf1110000_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1110001_9_00191
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells7e3a6c7b6b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells7e3a6c7b6b

open CertificateCells7e3a6c7b6b

theorem e24KC2PhiAboveLeaf1110001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL phiAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childLL phiAboveCell1110)))
    e24KC2PhiAboveLeaf1110001_c0 e24KC2PhiAboveLeaf1110001_c1 e24KC2PhiAboveLeaf1110001_c2
      e24KC2PhiAboveLeaf1110001_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1110010_9_00200
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa5efdb03f3

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsa5efdb03f3

open CertificateCellsa5efdb03f3

theorem e24KC2PhiAboveLeaf1110010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL phiAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childLL phiAboveCell1110)))
    e24KC2PhiAboveLeaf1110010_c0 e24KC2PhiAboveLeaf1110010_c1 e24KC2PhiAboveLeaf1110010_c2
      e24KC2PhiAboveLeaf1110010_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1110011_9_00208
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4f05b2093e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells4f05b2093e

open CertificateCells4f05b2093e

theorem e24KC2PhiAboveLeaf1110011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL phiAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childLL phiAboveCell1110)))
    e24KC2PhiAboveLeaf1110011_c0 e24KC2PhiAboveLeaf1110011_c1 e24KC2PhiAboveLeaf1110011_c2
      e24KC2PhiAboveLeaf1110011_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC6Phi Above Reconstruct
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa15368d7db

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsa15368d7db

open CertificateCellsa15368d7db

theorem e24KC2PhiAboveNode100101 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL phiAboveCell1001))
    e24KC2PhiAboveLeaf1001010 e24KC2PhiAboveLeaf1001011 e24KC2PhiAboveLeaf1001012
      e24KC2PhiAboveLeaf1001013

theorem e24KC2PhiAboveNode100110 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH phiAboveCell1001))
    e24KC2PhiAboveLeaf1001100 e24KC2PhiAboveLeaf1001101 e24KC2PhiAboveLeaf1001102
      e24KC2PhiAboveLeaf1001103

theorem e24KC2PhiAboveNode100111 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH phiAboveCell1001))
    e24KC2PhiAboveLeaf1001110 e24KC2PhiAboveLeaf1001111 e24KC2PhiAboveLeaf1001112
      e24KC2PhiAboveLeaf1001113

theorem e24KC2PhiAboveNode101000 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL phiAboveCell1010))
    e24KC2PhiAboveLeaf1010000 e24KC2PhiAboveLeaf1010001 e24KC2PhiAboveLeaf1010002
      e24KC2PhiAboveLeaf1010003

theorem e24KC2PhiAboveNode101001 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL phiAboveCell1010))
    e24KC2PhiAboveLeaf1010010 e24KC2PhiAboveLeaf1010011 e24KC2PhiAboveLeaf1010012
      e24KC2PhiAboveLeaf1010013

theorem e24KC2PhiAboveNode101010 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH phiAboveCell1010))
    e24KC2PhiAboveLeaf1010100 e24KC2PhiAboveLeaf1010101 e24KC2PhiAboveLeaf1010102
      e24KC2PhiAboveLeaf1010103

theorem e24KC2PhiAboveNode101011 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH phiAboveCell1010))
    e24KC2PhiAboveLeaf1010110 e24KC2PhiAboveLeaf1010111 e24KC2PhiAboveLeaf1010112
      e24KC2PhiAboveLeaf1010113

theorem e24KC2PhiAboveNode101100 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL phiAboveCell1011))
    e24KC2PhiAboveLeaf1011000 e24KC2PhiAboveLeaf1011001 e24KC2PhiAboveLeaf1011002
      e24KC2PhiAboveLeaf1011003

theorem e24KC2PhiAboveNode101101 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL phiAboveCell1011))
    e24KC2PhiAboveLeaf1011010 e24KC2PhiAboveLeaf1011011 e24KC2PhiAboveLeaf1011012
      e24KC2PhiAboveLeaf1011013

theorem e24KC2PhiAboveNode101110 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH phiAboveCell1011))
    e24KC2PhiAboveLeaf1011100 e24KC2PhiAboveLeaf1011101 e24KC2PhiAboveLeaf1011102
      e24KC2PhiAboveLeaf1011103

theorem e24KC2PhiAboveNode101111 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH phiAboveCell1011))
    e24KC2PhiAboveLeaf1011110 e24KC2PhiAboveLeaf1011111 e24KC2PhiAboveLeaf1011112
      e24KC2PhiAboveLeaf1011113

theorem e24KC2PhiAboveNode110000 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL phiAboveCell1100))
    e24KC2PhiAboveLeaf1100000 e24KC2PhiAboveLeaf1100001 e24KC2PhiAboveLeaf1100002
      e24KC2PhiAboveLeaf1100003

theorem e24KC2PhiAboveNode110001 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL phiAboveCell1100))
    e24KC2PhiAboveLeaf1100010 e24KC2PhiAboveLeaf1100011 e24KC2PhiAboveLeaf1100012
      e24KC2PhiAboveLeaf1100013

theorem e24KC2PhiAboveNode110010 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH phiAboveCell1100))
    e24KC2PhiAboveLeaf1100100 e24KC2PhiAboveLeaf1100101 e24KC2PhiAboveLeaf1100102
      e24KC2PhiAboveLeaf1100103

theorem e24KC2PhiAboveNode110011 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH phiAboveCell1100))
    e24KC2PhiAboveLeaf1100110 e24KC2PhiAboveLeaf1100111 e24KC2PhiAboveLeaf1100112
      e24KC2PhiAboveLeaf1100113

theorem e24KC2PhiAboveNode110013 :
    adaptiveCoverCheck 10 (childHH (childLH phiAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLH phiAboveCell1100))
    e24KC2PhiAboveLeaf1100130 e24KC2PhiAboveLeaf1100131 e24KC2PhiAboveLeaf1100132
      e24KC2PhiAboveLeaf1100133

theorem e24KC2PhiAboveNode110100 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL phiAboveCell1101))
    e24KC2PhiAboveLeaf1101000 e24KC2PhiAboveLeaf1101001 e24KC2PhiAboveLeaf1101002
      e24KC2PhiAboveLeaf1101003

theorem e24KC2PhiAboveNode110101 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL phiAboveCell1101))
    e24KC2PhiAboveLeaf1101010 e24KC2PhiAboveLeaf1101011 e24KC2PhiAboveLeaf1101012
      e24KC2PhiAboveLeaf1101013

theorem e24KC2PhiAboveNode110102 :
    adaptiveCoverCheck 10 (childHL (childLL phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLL phiAboveCell1101))
    e24KC2PhiAboveLeaf1101020 e24KC2PhiAboveLeaf1101021 e24KC2PhiAboveLeaf1101022
      e24KC2PhiAboveLeaf1101023

theorem e24KC2PhiAboveNode110103 :
    adaptiveCoverCheck 10 (childHH (childLL phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLL phiAboveCell1101))
    e24KC2PhiAboveLeaf1101030 e24KC2PhiAboveLeaf1101031 e24KC2PhiAboveLeaf1101032
      e24KC2PhiAboveLeaf1101033

theorem e24KC2PhiAboveNode110110 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH phiAboveCell1101))
    e24KC2PhiAboveLeaf1101100 e24KC2PhiAboveLeaf1101101 e24KC2PhiAboveLeaf1101102
      e24KC2PhiAboveLeaf1101103

theorem e24KC2PhiAboveNode110111 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH phiAboveCell1101))
    e24KC2PhiAboveLeaf1101110 e24KC2PhiAboveLeaf1101111 e24KC2PhiAboveLeaf1101112
      e24KC2PhiAboveLeaf1101113

theorem e24KC2PhiAboveNode110112 :
    adaptiveCoverCheck 10 (childHL (childLH phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLH phiAboveCell1101))
    e24KC2PhiAboveLeaf1101120 e24KC2PhiAboveLeaf1101121 e24KC2PhiAboveLeaf1101122
      e24KC2PhiAboveLeaf1101123

theorem e24KC2PhiAboveNode110113 :
    adaptiveCoverCheck 10 (childHH (childLH phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLH phiAboveCell1101))
    e24KC2PhiAboveLeaf1101130 e24KC2PhiAboveLeaf1101131 e24KC2PhiAboveLeaf1101132
      e24KC2PhiAboveLeaf1101133

theorem e24KC2PhiAboveNode111000 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL phiAboveCell1110))
    e24KC2PhiAboveLeaf1110000 e24KC2PhiAboveLeaf1110001 e24KC2PhiAboveLeaf1110002
      e24KC2PhiAboveLeaf1110003

theorem e24KC2PhiAboveNode111001 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL phiAboveCell1110))
    e24KC2PhiAboveLeaf1110010 e24KC2PhiAboveLeaf1110011 e24KC2PhiAboveLeaf1110012
      e24KC2PhiAboveLeaf1110013

theorem e24KC2PhiAboveNode111002 :
    adaptiveCoverCheck 10 (childHL (childLL phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLL phiAboveCell1110))
    e24KC2PhiAboveLeaf1110020 e24KC2PhiAboveLeaf1110021 e24KC2PhiAboveLeaf1110022
      e24KC2PhiAboveLeaf1110023

theorem e24KC2PhiAboveNode111003 :
    adaptiveCoverCheck 10 (childHH (childLL phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLL phiAboveCell1110))
    e24KC2PhiAboveLeaf1110030 e24KC2PhiAboveLeaf1110031 e24KC2PhiAboveLeaf1110032
      e24KC2PhiAboveLeaf1110033

theorem e24KC2PhiAboveNode111010 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH phiAboveCell1110))
    e24KC2PhiAboveLeaf1110100 e24KC2PhiAboveLeaf1110101 e24KC2PhiAboveLeaf1110102
      e24KC2PhiAboveLeaf1110103

theorem e24KC2PhiAboveNode111011 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH phiAboveCell1110))
    e24KC2PhiAboveLeaf1110110 e24KC2PhiAboveLeaf1110111 e24KC2PhiAboveLeaf1110112
      e24KC2PhiAboveLeaf1110113

theorem e24KC2PhiAboveNode111012 :
    adaptiveCoverCheck 10 (childHL (childLH phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLH phiAboveCell1110))
    e24KC2PhiAboveLeaf1110120 e24KC2PhiAboveLeaf1110121 e24KC2PhiAboveLeaf1110122
      e24KC2PhiAboveLeaf1110123

theorem e24KC2PhiAboveNode111013 :
    adaptiveCoverCheck 10 (childHH (childLH phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLH phiAboveCell1110))
    e24KC2PhiAboveLeaf1110130 e24KC2PhiAboveLeaf1110131 e24KC2PhiAboveLeaf1110132
      e24KC2PhiAboveLeaf1110133

theorem e24KC2PhiAboveNode111100 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL phiAboveCell1111))
    e24KC2PhiAboveLeaf1111000 e24KC2PhiAboveLeaf1111001 e24KC2PhiAboveLeaf1111002
      e24KC2PhiAboveLeaf1111003

theorem e24KC2PhiAboveNode111101 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL phiAboveCell1111))
    e24KC2PhiAboveLeaf1111010 e24KC2PhiAboveLeaf1111011 e24KC2PhiAboveLeaf1111012
      e24KC2PhiAboveLeaf1111013

theorem e24KC2PhiAboveNode111102 :
    adaptiveCoverCheck 10 (childHL (childLL phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLL phiAboveCell1111))
    e24KC2PhiAboveLeaf1111020 e24KC2PhiAboveLeaf1111021 e24KC2PhiAboveLeaf1111022
      e24KC2PhiAboveLeaf1111023

theorem e24KC2PhiAboveNode111103 :
    adaptiveCoverCheck 10 (childHH (childLL phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLL phiAboveCell1111))
    e24KC2PhiAboveLeaf1111030 e24KC2PhiAboveLeaf1111031 e24KC2PhiAboveLeaf1111032
      e24KC2PhiAboveLeaf1111033

theorem e24KC2PhiAboveNode111110 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH phiAboveCell1111))
    e24KC2PhiAboveLeaf1111100 e24KC2PhiAboveLeaf1111101 e24KC2PhiAboveLeaf1111102
      e24KC2PhiAboveLeaf1111103

theorem e24KC2PhiAboveNode111111 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH phiAboveCell1111))
    e24KC2PhiAboveLeaf1111110 e24KC2PhiAboveLeaf1111111 e24KC2PhiAboveLeaf1111112
      e24KC2PhiAboveLeaf1111113

theorem e24KC2PhiAboveNode111112 :
    adaptiveCoverCheck 10 (childHL (childLH phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLH phiAboveCell1111))
    e24KC2PhiAboveLeaf1111120 e24KC2PhiAboveLeaf1111121 e24KC2PhiAboveLeaf1111122
      e24KC2PhiAboveLeaf1111123

theorem e24KC2PhiAboveNode111113 :
    adaptiveCoverCheck 10 (childHH (childLH phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLH phiAboveCell1111))
    e24KC2PhiAboveLeaf1111130 e24KC2PhiAboveLeaf1111131 e24KC2PhiAboveLeaf1111132
      e24KC2PhiAboveLeaf1111133

theorem e24KC2PhiAboveNode01011 :
    adaptiveCoverCheck 11 (childLH phiAboveCell0101) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell0101)
    e24KC2PhiAboveLeaf010110 e24KC2PhiAboveLeaf010111 e24KC2PhiAboveLeaf010112
      e24KC2PhiAboveLeaf010113

theorem e24KC2PhiAboveNode01100 :
    adaptiveCoverCheck 11 (childLL phiAboveCell0110) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell0110)
    e24KC2PhiAboveLeaf011000 e24KC2PhiAboveLeaf011001 e24KC2PhiAboveLeaf011002
      e24KC2PhiAboveLeaf011003

theorem e24KC2PhiAboveNode01101 :
    adaptiveCoverCheck 11 (childLH phiAboveCell0110) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell0110)
    e24KC2PhiAboveLeaf011010 e24KC2PhiAboveLeaf011011 e24KC2PhiAboveLeaf011012
      e24KC2PhiAboveLeaf011013

theorem e24KC2PhiAboveNode01110 :
    adaptiveCoverCheck 11 (childLL phiAboveCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell0111)
    e24KC2PhiAboveLeaf011100 e24KC2PhiAboveLeaf011101 e24KC2PhiAboveLeaf011102
      e24KC2PhiAboveLeaf011103

theorem e24KC2PhiAboveNode01111 :
    adaptiveCoverCheck 11 (childLH phiAboveCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell0111)
    e24KC2PhiAboveLeaf011110 e24KC2PhiAboveLeaf011111 e24KC2PhiAboveLeaf011112
      e24KC2PhiAboveLeaf011113

theorem e24KC2PhiAboveNode10000 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1000)
    e24KC2PhiAboveLeaf100000 e24KC2PhiAboveLeaf100001 e24KC2PhiAboveLeaf100002
      e24KC2PhiAboveLeaf100003

theorem e24KC2PhiAboveNode10001 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1000)
    e24KC2PhiAboveLeaf100010 e24KC2PhiAboveLeaf100011 e24KC2PhiAboveLeaf100012
      e24KC2PhiAboveLeaf100013

theorem e24KC2PhiAboveNode10010 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1001)
    e24KC2PhiAboveLeaf100100 e24KC2PhiAboveNode100101 e24KC2PhiAboveLeaf100102
      e24KC2PhiAboveLeaf100103

theorem e24KC2PhiAboveNode10011 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1001)
    e24KC2PhiAboveNode100110 e24KC2PhiAboveNode100111 e24KC2PhiAboveLeaf100112
      e24KC2PhiAboveLeaf100113

theorem e24KC2PhiAboveNode10100 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1010)
    e24KC2PhiAboveNode101000 e24KC2PhiAboveNode101001 e24KC2PhiAboveLeaf101002
      e24KC2PhiAboveLeaf101003

theorem e24KC2PhiAboveNode10101 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1010)
    e24KC2PhiAboveNode101010 e24KC2PhiAboveNode101011 e24KC2PhiAboveLeaf101012
      e24KC2PhiAboveLeaf101013

theorem e24KC2PhiAboveNode10110 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1011)
    e24KC2PhiAboveNode101100 e24KC2PhiAboveNode101101 e24KC2PhiAboveLeaf101102
      e24KC2PhiAboveLeaf101103

theorem e24KC2PhiAboveNode10111 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1011)
    e24KC2PhiAboveNode101110 e24KC2PhiAboveNode101111 e24KC2PhiAboveLeaf101112
      e24KC2PhiAboveLeaf101113

theorem e24KC2PhiAboveNode10113 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH phiAboveCell1011)
    e24KC2PhiAboveLeaf101130 e24KC2PhiAboveLeaf101131 e24KC2PhiAboveLeaf101132
      e24KC2PhiAboveLeaf101133

theorem e24KC2PhiAboveNode11000 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1100)
    e24KC2PhiAboveNode110000 e24KC2PhiAboveNode110001 e24KC2PhiAboveLeaf110002
      e24KC2PhiAboveLeaf110003

theorem e24KC2PhiAboveNode11001 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1100)
    e24KC2PhiAboveNode110010 e24KC2PhiAboveNode110011 e24KC2PhiAboveLeaf110012
      e24KC2PhiAboveNode110013

theorem e24KC2PhiAboveNode11002 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL phiAboveCell1100)
    e24KC2PhiAboveLeaf110020 e24KC2PhiAboveLeaf110021 e24KC2PhiAboveLeaf110022
      e24KC2PhiAboveLeaf110023

theorem e24KC2PhiAboveNode11003 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH phiAboveCell1100)
    e24KC2PhiAboveLeaf110030 e24KC2PhiAboveLeaf110031 e24KC2PhiAboveLeaf110032
      e24KC2PhiAboveLeaf110033

theorem e24KC2PhiAboveNode11010 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1101)
    e24KC2PhiAboveNode110100 e24KC2PhiAboveNode110101 e24KC2PhiAboveNode110102
      e24KC2PhiAboveNode110103

theorem e24KC2PhiAboveNode11011 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1101)
    e24KC2PhiAboveNode110110 e24KC2PhiAboveNode110111 e24KC2PhiAboveNode110112
      e24KC2PhiAboveNode110113

theorem e24KC2PhiAboveNode11012 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL phiAboveCell1101)
    e24KC2PhiAboveLeaf110120 e24KC2PhiAboveLeaf110121 e24KC2PhiAboveLeaf110122
      e24KC2PhiAboveLeaf110123

theorem e24KC2PhiAboveNode11013 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH phiAboveCell1101)
    e24KC2PhiAboveLeaf110130 e24KC2PhiAboveLeaf110131 e24KC2PhiAboveLeaf110132
      e24KC2PhiAboveLeaf110133

theorem e24KC2PhiAboveNode11100 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1110)
    e24KC2PhiAboveNode111000 e24KC2PhiAboveNode111001 e24KC2PhiAboveNode111002
      e24KC2PhiAboveNode111003

theorem e24KC2PhiAboveNode11101 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1110)
    e24KC2PhiAboveNode111010 e24KC2PhiAboveNode111011 e24KC2PhiAboveNode111012
      e24KC2PhiAboveNode111013

theorem e24KC2PhiAboveNode11102 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL phiAboveCell1110)
    e24KC2PhiAboveLeaf111020 e24KC2PhiAboveLeaf111021 e24KC2PhiAboveLeaf111022
      e24KC2PhiAboveLeaf111023

theorem e24KC2PhiAboveNode11103 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH phiAboveCell1110)
    e24KC2PhiAboveLeaf111030 e24KC2PhiAboveLeaf111031 e24KC2PhiAboveLeaf111032
      e24KC2PhiAboveLeaf111033

theorem e24KC2PhiAboveNode11110 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1111)
    e24KC2PhiAboveNode111100 e24KC2PhiAboveNode111101 e24KC2PhiAboveNode111102
      e24KC2PhiAboveNode111103

theorem e24KC2PhiAboveNode11111 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1111)
    e24KC2PhiAboveNode111110 e24KC2PhiAboveNode111111 e24KC2PhiAboveNode111112
      e24KC2PhiAboveNode111113

theorem e24KC2PhiAboveNode11112 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL phiAboveCell1111)
    e24KC2PhiAboveLeaf111120 e24KC2PhiAboveLeaf111121 e24KC2PhiAboveLeaf111122
      e24KC2PhiAboveLeaf111123

theorem e24KC2PhiAboveNode11113 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH phiAboveCell1111)
    e24KC2PhiAboveLeaf111130 e24KC2PhiAboveLeaf111131 e24KC2PhiAboveLeaf111132
      e24KC2PhiAboveLeaf111133

theorem e24KC2PhiAboveNode0000 :
    adaptiveCoverCheck 12 phiAboveCell0000 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0000
    e24KC2PhiAboveLeaf00000 e24KC2PhiAboveLeaf00001 e24KC2PhiAboveLeaf00002 e24KC2PhiAboveLeaf00003

theorem e24KC2PhiAboveNode0001 :
    adaptiveCoverCheck 12 phiAboveCell0001 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0001
    e24KC2PhiAboveLeaf00010 e24KC2PhiAboveLeaf00011 e24KC2PhiAboveLeaf00012 e24KC2PhiAboveLeaf00013

theorem e24KC2PhiAboveNode0010 :
    adaptiveCoverCheck 12 phiAboveCell0010 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0010
    e24KC2PhiAboveLeaf00100 e24KC2PhiAboveLeaf00101 e24KC2PhiAboveLeaf00102 e24KC2PhiAboveLeaf00103

theorem e24KC2PhiAboveNode0011 :
    adaptiveCoverCheck 12 phiAboveCell0011 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0011
    e24KC2PhiAboveLeaf00110 e24KC2PhiAboveLeaf00111 e24KC2PhiAboveLeaf00112 e24KC2PhiAboveLeaf00113

theorem e24KC2PhiAboveNode0100 :
    adaptiveCoverCheck 12 phiAboveCell0100 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0100
    e24KC2PhiAboveLeaf01000 e24KC2PhiAboveLeaf01001 e24KC2PhiAboveLeaf01002 e24KC2PhiAboveLeaf01003

theorem e24KC2PhiAboveNode0101 :
    adaptiveCoverCheck 12 phiAboveCell0101 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0101
    e24KC2PhiAboveLeaf01010 e24KC2PhiAboveNode01011 e24KC2PhiAboveLeaf01012 e24KC2PhiAboveLeaf01013

theorem e24KC2PhiAboveNode0110 :
    adaptiveCoverCheck 12 phiAboveCell0110 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0110
    e24KC2PhiAboveNode01100 e24KC2PhiAboveNode01101 e24KC2PhiAboveLeaf01102 e24KC2PhiAboveLeaf01103

theorem e24KC2PhiAboveNode0111 :
    adaptiveCoverCheck 12 phiAboveCell0111 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0111
    e24KC2PhiAboveNode01110 e24KC2PhiAboveNode01111 e24KC2PhiAboveLeaf01112 e24KC2PhiAboveLeaf01113

theorem e24KC2PhiAboveNode1000 :
    adaptiveCoverCheck 12 phiAboveCell1000 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1000
    e24KC2PhiAboveNode10000 e24KC2PhiAboveNode10001 e24KC2PhiAboveLeaf10002 e24KC2PhiAboveLeaf10003

theorem e24KC2PhiAboveNode1001 :
    adaptiveCoverCheck 12 phiAboveCell1001 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1001
    e24KC2PhiAboveNode10010 e24KC2PhiAboveNode10011 e24KC2PhiAboveLeaf10012 e24KC2PhiAboveLeaf10013

theorem e24KC2PhiAboveNode1002 :
    adaptiveCoverCheck 12 phiAboveCell1002 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1002
    e24KC2PhiAboveLeaf10020 e24KC2PhiAboveLeaf10021 e24KC2PhiAboveLeaf10022 e24KC2PhiAboveLeaf10023

theorem e24KC2PhiAboveNode1003 :
    adaptiveCoverCheck 12 phiAboveCell1003 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1003
    e24KC2PhiAboveLeaf10030 e24KC2PhiAboveLeaf10031 e24KC2PhiAboveLeaf10032 e24KC2PhiAboveLeaf10033

theorem e24KC2PhiAboveNode1010 :
    adaptiveCoverCheck 12 phiAboveCell1010 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1010
    e24KC2PhiAboveNode10100 e24KC2PhiAboveNode10101 e24KC2PhiAboveLeaf10102 e24KC2PhiAboveLeaf10103

theorem e24KC2PhiAboveNode1011 :
    adaptiveCoverCheck 12 phiAboveCell1011 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1011
    e24KC2PhiAboveNode10110 e24KC2PhiAboveNode10111 e24KC2PhiAboveLeaf10112 e24KC2PhiAboveNode10113

theorem e24KC2PhiAboveNode1012 :
    adaptiveCoverCheck 12 phiAboveCell1012 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1012
    e24KC2PhiAboveLeaf10120 e24KC2PhiAboveLeaf10121 e24KC2PhiAboveLeaf10122 e24KC2PhiAboveLeaf10123

theorem e24KC2PhiAboveNode1013 :
    adaptiveCoverCheck 12 phiAboveCell1013 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1013
    e24KC2PhiAboveLeaf10130 e24KC2PhiAboveLeaf10131 e24KC2PhiAboveLeaf10132 e24KC2PhiAboveLeaf10133

theorem e24KC2PhiAboveNode1100 :
    adaptiveCoverCheck 12 phiAboveCell1100 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1100
    e24KC2PhiAboveNode11000 e24KC2PhiAboveNode11001 e24KC2PhiAboveNode11002 e24KC2PhiAboveNode11003

theorem e24KC2PhiAboveNode1101 :
    adaptiveCoverCheck 12 phiAboveCell1101 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1101
    e24KC2PhiAboveNode11010 e24KC2PhiAboveNode11011 e24KC2PhiAboveNode11012 e24KC2PhiAboveNode11013

theorem e24KC2PhiAboveNode1102 :
    adaptiveCoverCheck 12 phiAboveCell1102 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1102
    e24KC2PhiAboveLeaf11020 e24KC2PhiAboveLeaf11021 e24KC2PhiAboveLeaf11022 e24KC2PhiAboveLeaf11023

theorem e24KC2PhiAboveNode1103 :
    adaptiveCoverCheck 12 phiAboveCell1103 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1103
    e24KC2PhiAboveLeaf11030 e24KC2PhiAboveLeaf11031 e24KC2PhiAboveLeaf11032 e24KC2PhiAboveLeaf11033

theorem e24KC2PhiAboveNode1110 :
    adaptiveCoverCheck 12 phiAboveCell1110 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1110
    e24KC2PhiAboveNode11100 e24KC2PhiAboveNode11101 e24KC2PhiAboveNode11102 e24KC2PhiAboveNode11103

theorem e24KC2PhiAboveNode1111 :
    adaptiveCoverCheck 12 phiAboveCell1111 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1111
    e24KC2PhiAboveNode11110 e24KC2PhiAboveNode11111 e24KC2PhiAboveNode11112 e24KC2PhiAboveNode11113

theorem e24KC2PhiAboveNode1112 :
    adaptiveCoverCheck 12 phiAboveCell1112 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1112
    e24KC2PhiAboveLeaf11120 e24KC2PhiAboveLeaf11121 e24KC2PhiAboveLeaf11122 e24KC2PhiAboveLeaf11123

theorem e24KC2PhiAboveNode1113 :
    adaptiveCoverCheck 12 phiAboveCell1113 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1113
    e24KC2PhiAboveLeaf11130 e24KC2PhiAboveLeaf11131 e24KC2PhiAboveLeaf11132 e24KC2PhiAboveLeaf11133

theorem e24KC2PhiAboveNode000 :
    adaptiveCoverCheck 13 (childLL (childLL (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveNode0000 e24KC2PhiAboveNode0001 e24KC2PhiAboveLeaf0002 e24KC2PhiAboveLeaf0003

theorem e24KC2PhiAboveNode001 :
    adaptiveCoverCheck 13 (childLH (childLL (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveNode0010 e24KC2PhiAboveNode0011 e24KC2PhiAboveLeaf0012 e24KC2PhiAboveLeaf0013

theorem e24KC2PhiAboveNode003 :
    adaptiveCoverCheck 13 (childHH (childLL (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childLL (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf0030 e24KC2PhiAboveLeaf0031 e24KC2PhiAboveLeaf0032 e24KC2PhiAboveLeaf0033

theorem e24KC2PhiAboveNode010 :
    adaptiveCoverCheck 13 (childLL (childLH (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveNode0100 e24KC2PhiAboveNode0101 e24KC2PhiAboveLeaf0102 e24KC2PhiAboveLeaf0103

theorem e24KC2PhiAboveNode011 :
    adaptiveCoverCheck 13 (childLH (childLH (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveNode0110 e24KC2PhiAboveNode0111 e24KC2PhiAboveLeaf0112 e24KC2PhiAboveLeaf0113

theorem e24KC2PhiAboveNode012 :
    adaptiveCoverCheck 13 (childHL (childLH (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childLH (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf0120 e24KC2PhiAboveLeaf0121 e24KC2PhiAboveLeaf0122 e24KC2PhiAboveLeaf0123

theorem e24KC2PhiAboveNode013 :
    adaptiveCoverCheck 13 (childHH (childLH (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childLH (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf0130 e24KC2PhiAboveLeaf0131 e24KC2PhiAboveLeaf0132 e24KC2PhiAboveLeaf0133

theorem e24KC2PhiAboveNode100 :
    adaptiveCoverCheck 13 (childLL (childLL (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveNode1000 e24KC2PhiAboveNode1001 e24KC2PhiAboveNode1002 e24KC2PhiAboveNode1003

theorem e24KC2PhiAboveNode101 :
    adaptiveCoverCheck 13 (childLH (childLL (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveNode1010 e24KC2PhiAboveNode1011 e24KC2PhiAboveNode1012 e24KC2PhiAboveNode1013

theorem e24KC2PhiAboveNode102 :
    adaptiveCoverCheck 13 (childHL (childLL (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childLL (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf1020 e24KC2PhiAboveLeaf1021 e24KC2PhiAboveLeaf1022 e24KC2PhiAboveLeaf1023

theorem e24KC2PhiAboveNode103 :
    adaptiveCoverCheck 13 (childHH (childLL (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childLL (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf1030 e24KC2PhiAboveLeaf1031 e24KC2PhiAboveLeaf1032 e24KC2PhiAboveLeaf1033

theorem e24KC2PhiAboveNode110 :
    adaptiveCoverCheck 13 (childLL (childLH (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveNode1100 e24KC2PhiAboveNode1101 e24KC2PhiAboveNode1102 e24KC2PhiAboveNode1103

theorem e24KC2PhiAboveNode111 :
    adaptiveCoverCheck 13 (childLH (childLH (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveNode1110 e24KC2PhiAboveNode1111 e24KC2PhiAboveNode1112 e24KC2PhiAboveNode1113

theorem e24KC2PhiAboveNode112 :
    adaptiveCoverCheck 13 (childHL (childLH (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childLH (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf1120 e24KC2PhiAboveLeaf1121 e24KC2PhiAboveLeaf1122 e24KC2PhiAboveLeaf1123

theorem e24KC2PhiAboveNode113 :
    adaptiveCoverCheck 13 (childHH (childLH (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childLH (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf1130 e24KC2PhiAboveLeaf1131 e24KC2PhiAboveLeaf1132 e24KC2PhiAboveLeaf1133

theorem e24KC2PhiAboveNode00 :
    adaptiveCoverCheck 14 (childLL (childLL e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL (childLL e24PhiAboveRoot))
    e24KC2PhiAboveNode000 e24KC2PhiAboveNode001 e24KC2PhiAboveLeaf002 e24KC2PhiAboveNode003

theorem e24KC2PhiAboveNode01 :
    adaptiveCoverCheck 14 (childLH (childLL e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH (childLL e24PhiAboveRoot))
    e24KC2PhiAboveNode010 e24KC2PhiAboveNode011 e24KC2PhiAboveNode012 e24KC2PhiAboveNode013

theorem e24KC2PhiAboveNode03 :
    adaptiveCoverCheck 14 (childHH (childLL e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH (childLL e24PhiAboveRoot))
    e24KC2PhiAboveLeaf030 e24KC2PhiAboveLeaf031 e24KC2PhiAboveLeaf032 e24KC2PhiAboveLeaf033

theorem e24KC2PhiAboveNode10 :
    adaptiveCoverCheck 14 (childLL (childLH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL (childLH e24PhiAboveRoot))
    e24KC2PhiAboveNode100 e24KC2PhiAboveNode101 e24KC2PhiAboveNode102 e24KC2PhiAboveNode103

theorem e24KC2PhiAboveNode11 :
    adaptiveCoverCheck 14 (childLH (childLH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH (childLH e24PhiAboveRoot))
    e24KC2PhiAboveNode110 e24KC2PhiAboveNode111 e24KC2PhiAboveNode112 e24KC2PhiAboveNode113

theorem e24KC2PhiAboveNode12 :
    adaptiveCoverCheck 14 (childHL (childLH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL (childLH e24PhiAboveRoot))
    e24KC2PhiAboveLeaf120 e24KC2PhiAboveLeaf121 e24KC2PhiAboveLeaf122 e24KC2PhiAboveLeaf123

theorem e24KC2PhiAboveNode13 :
    adaptiveCoverCheck 14 (childHH (childLH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH (childLH e24PhiAboveRoot))
    e24KC2PhiAboveLeaf130 e24KC2PhiAboveLeaf131 e24KC2PhiAboveLeaf132 e24KC2PhiAboveLeaf133

theorem e24KC2PhiAboveNode30 :
    adaptiveCoverCheck 14 (childLL (childHH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL (childHH e24PhiAboveRoot))
    e24KC2PhiAboveLeaf300 e24KC2PhiAboveLeaf301 e24KC2PhiAboveLeaf302 e24KC2PhiAboveLeaf303

theorem e24KC2PhiAboveNode31 :
    adaptiveCoverCheck 14 (childLH (childHH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH (childHH e24PhiAboveRoot))
    e24KC2PhiAboveLeaf310 e24KC2PhiAboveLeaf311 e24KC2PhiAboveLeaf312 e24KC2PhiAboveLeaf313

theorem e24KC2PhiAboveNode33 :
    adaptiveCoverCheck 14 (childHH (childHH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH (childHH e24PhiAboveRoot))
    e24KC2PhiAboveLeaf330 e24KC2PhiAboveLeaf331 e24KC2PhiAboveLeaf332 e24KC2PhiAboveLeaf333

theorem e24KC2PhiAboveNode0 :
    adaptiveCoverCheck 15 (childLL e24PhiAboveRoot) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLL e24PhiAboveRoot)
    e24KC2PhiAboveNode00 e24KC2PhiAboveNode01 e24KC2PhiAboveLeaf02 e24KC2PhiAboveNode03

theorem e24KC2PhiAboveNode1 :
    adaptiveCoverCheck 15 (childLH e24PhiAboveRoot) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLH e24PhiAboveRoot)
    e24KC2PhiAboveNode10 e24KC2PhiAboveNode11 e24KC2PhiAboveNode12 e24KC2PhiAboveNode13

theorem e24KC2PhiAboveNode3 :
    adaptiveCoverCheck 15 (childHH e24PhiAboveRoot) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHH e24PhiAboveRoot)
    e24KC2PhiAboveNode30 e24KC2PhiAboveNode31 e24KC2PhiAboveLeaf32 e24KC2PhiAboveNode33

theorem e24KC2PhiAboveNodeROOT :
    adaptiveCoverCheck 16 e24PhiAboveRoot = true :=
  adaptiveCoverCheck_succ_of_children 15 e24PhiAboveRoot
    e24KC2PhiAboveNode0 e24KC2PhiAboveNode1 e24KC2PhiAboveLeaf2 e24KC2PhiAboveNode3

theorem e24PhiAboveKernelCheck :
    adaptiveCoverCheck 16 e24PhiAboveRoot = true :=
  e24KC2PhiAboveNodeROOT

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33203_9_00246
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells12ecbb1984

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells12ecbb1984

open CertificateCells12ecbb1984

theorem e24KC2PhiBelowLeaf33203 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3320) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childHH phiBelowCell3320)
    e24KC2PhiBelowLeaf33203_c0 e24KC2PhiBelowLeaf33203_c1 e24KC2PhiBelowLeaf33203_c2
      e24KC2PhiBelowLeaf33203_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33221_9_00260
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf9b1d22c2c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsf9b1d22c2c

open CertificateCellsf9b1d22c2c

theorem e24KC2PhiBelowLeaf33221 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3322) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLH phiBelowCell3322)
    e24KC2PhiBelowLeaf33221_c0 e24KC2PhiBelowLeaf33221_c1 e24KC2PhiBelowLeaf33221_c2
      e24KC2PhiBelowLeaf33221_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33223_9_00269
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5481d87062

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells5481d87062

open CertificateCells5481d87062

theorem e24KC2PhiBelowLeaf33223 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3322) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childHH phiBelowCell3322)
    e24KC2PhiBelowLeaf33223_c0 e24KC2PhiBelowLeaf33223_c1 e24KC2PhiBelowLeaf33223_c2
      e24KC2PhiBelowLeaf33223_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33230_c2_8_00278
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc99c114252

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsc99c114252

open CertificateCellsc99c114252

theorem e24KC2PhiBelowLeaf33230_c2 :
    adaptiveCoverCheck 8 (childHL (childLL phiBelowCell3323)) = true :=
  adaptiveCoverCheck_succ_of_children 7 (childHL (childLL phiBelowCell3323))
    e24KC2PhiBelowLeaf33230_c2_c0 e24KC2PhiBelowLeaf33230_c2_c1 e24KC2PhiBelowLeaf33230_c2_c2
      e24KC2PhiBelowLeaf33230_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33230_c3_8_00284
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells85102f4bff

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells85102f4bff

open CertificateCells85102f4bff

theorem e24KC2PhiBelowLeaf33230_c3 :
    adaptiveCoverCheck 8 (childHH (childLL phiBelowCell3323)) = true :=
  adaptiveCoverCheck_succ_of_children 7 (childHH (childLL phiBelowCell3323))
    e24KC2PhiBelowLeaf33230_c3_c0 e24KC2PhiBelowLeaf33230_c3_c1 e24KC2PhiBelowLeaf33230_c3_c2
      e24KC2PhiBelowLeaf33230_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33230_9_00285
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd7423e4c3b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsd7423e4c3b

open CertificateCellsd7423e4c3b

theorem e24KC2PhiBelowLeaf33230 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3323) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLL phiBelowCell3323)
    e24KC2PhiBelowLeaf33230_c0 e24KC2PhiBelowLeaf33230_c1 e24KC2PhiBelowLeaf33230_c2
      e24KC2PhiBelowLeaf33230_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33232_c0_8_00294
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells8ae9088aab

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells8ae9088aab

open CertificateCells8ae9088aab

theorem e24KC2PhiBelowLeaf33232_c0 :
    adaptiveCoverCheck 8 (childLL (childHL phiBelowCell3323)) = true :=
  adaptiveCoverCheck_succ_of_children 7 (childLL (childHL phiBelowCell3323))
    e24KC2PhiBelowLeaf33232_c0_c0 e24KC2PhiBelowLeaf33232_c0_c1 e24KC2PhiBelowLeaf33232_c0_c2
      e24KC2PhiBelowLeaf33232_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33232_c1_c0_7_00301
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb8a79b56b3

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsb8a79b56b3

open CertificateCellsb8a79b56b3

theorem e24KC2PhiBelowLeaf33232_c1_c0 :
    adaptiveCoverCheck 7 (childLL (childLH (childHL phiBelowCell3323))) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childHL phiBelowCell3323)))
    e24KC2PhiBelowLeaf33232_c1_c0_c0 e24KC2PhiBelowLeaf33232_c1_c0_c1
      e24KC2PhiBelowLeaf33232_c1_c0_c2 e24KC2PhiBelowLeaf33232_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33232_c1_c2_7_00308
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells13ae325d6d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells13ae325d6d

open CertificateCells13ae325d6d

theorem e24KC2PhiBelowLeaf33232_c1_c2 :
    adaptiveCoverCheck 7 (childHL (childLH (childHL phiBelowCell3323))) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childHL phiBelowCell3323)))
    e24KC2PhiBelowLeaf33232_c1_c2_c0 e24KC2PhiBelowLeaf33232_c1_c2_c1
      e24KC2PhiBelowLeaf33232_c1_c2_c2 e24KC2PhiBelowLeaf33232_c1_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33232_c1_c3_7_00314
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6add7bae04

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells6add7bae04

open CertificateCells6add7bae04

theorem e24KC2PhiBelowLeaf33232_c1_c3 :
    adaptiveCoverCheck 7 (childHH (childLH (childHL phiBelowCell3323))) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childHL phiBelowCell3323)))
    e24KC2PhiBelowLeaf33232_c1_c3_c0 e24KC2PhiBelowLeaf33232_c1_c3_c1
      e24KC2PhiBelowLeaf33232_c1_c3_c2 e24KC2PhiBelowLeaf33232_c1_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33232_c1_8_00315
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellscd1d17c9b4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellscd1d17c9b4

open CertificateCellscd1d17c9b4

theorem e24KC2PhiBelowLeaf33232_c1 :
    adaptiveCoverCheck 8 (childLH (childHL phiBelowCell3323)) = true :=
  adaptiveCoverCheck_succ_of_children 7 (childLH (childHL phiBelowCell3323))
    e24KC2PhiBelowLeaf33232_c1_c0 e24KC2PhiBelowLeaf33232_c1_c1 e24KC2PhiBelowLeaf33232_c1_c2
      e24KC2PhiBelowLeaf33232_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33232_c3_c1_c1_6_00326
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells709ea69226

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells709ea69226

open CertificateCells709ea69226

theorem e24KC2PhiBelowLeaf33232_c3_c1_c1 :
    adaptiveCoverCheck 6 phiBelowCell33232311 = true :=
  adaptiveCoverCheck_succ_of_children 5 phiBelowCell33232311
    e24KC2PhiBelowLeaf33232_c3_c1_c1_c0 e24KC2PhiBelowLeaf33232_c3_c1_c1_c1
      e24KC2PhiBelowLeaf33232_c3_c1_c1_c2 e24KC2PhiBelowLeaf33232_c3_c1_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33232_c3_c1_c3_6_00333
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsade8569b0a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsade8569b0a

open CertificateCellsade8569b0a

theorem e24KC2PhiBelowLeaf33232_c3_c1_c3 :
    adaptiveCoverCheck 6 phiBelowCell33232313 = true :=
  adaptiveCoverCheck_succ_of_children 5 phiBelowCell33232313
    e24KC2PhiBelowLeaf33232_c3_c1_c3_c0 e24KC2PhiBelowLeaf33232_c3_c1_c3_c1
      e24KC2PhiBelowLeaf33232_c3_c1_c3_c2 e24KC2PhiBelowLeaf33232_c3_c1_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33232_c3_c1_7_00334
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsfece773e85

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsfece773e85

open CertificateCellsfece773e85

theorem e24KC2PhiBelowLeaf33232_c3_c1 :
    adaptiveCoverCheck 7 (childLH (childHH (childHL phiBelowCell3323))) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childHL phiBelowCell3323)))
    e24KC2PhiBelowLeaf33232_c3_c1_c0 e24KC2PhiBelowLeaf33232_c3_c1_c1
      e24KC2PhiBelowLeaf33232_c3_c1_c2 e24KC2PhiBelowLeaf33232_c3_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33232_c3_c3_c1_6_00343
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse593ec4a84

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse593ec4a84

open CertificateCellse593ec4a84

theorem e24KC2PhiBelowLeaf33232_c3_c3_c1 :
    adaptiveCoverCheck 6 phiBelowCell33232331 = true :=
  adaptiveCoverCheck_succ_of_children 5 phiBelowCell33232331
    e24KC2PhiBelowLeaf33232_c3_c3_c1_c0 e24KC2PhiBelowLeaf33232_c3_c3_c1_c1
      e24KC2PhiBelowLeaf33232_c3_c3_c1_c2 e24KC2PhiBelowLeaf33232_c3_c3_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33232_c3_c3_7_00346
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0ccc164bd1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells0ccc164bd1

open CertificateCells0ccc164bd1

theorem e24KC2PhiBelowLeaf33232_c3_c3 :
    adaptiveCoverCheck 7 (childHH (childHH (childHL phiBelowCell3323))) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childHL phiBelowCell3323)))
    e24KC2PhiBelowLeaf33232_c3_c3_c0 e24KC2PhiBelowLeaf33232_c3_c3_c1
      e24KC2PhiBelowLeaf33232_c3_c3_c2 e24KC2PhiBelowLeaf33232_c3_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33232_c3_8_00347
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells072df6b25f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells072df6b25f

open CertificateCells072df6b25f

theorem e24KC2PhiBelowLeaf33232_c3 :
    adaptiveCoverCheck 8 (childHH (childHL phiBelowCell3323)) = true :=
  adaptiveCoverCheck_succ_of_children 7 (childHH (childHL phiBelowCell3323))
    e24KC2PhiBelowLeaf33232_c3_c0 e24KC2PhiBelowLeaf33232_c3_c1 e24KC2PhiBelowLeaf33232_c3_c2
      e24KC2PhiBelowLeaf33232_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33232_9_00348
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells215f6c9ebd

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells215f6c9ebd

open CertificateCells215f6c9ebd

theorem e24KC2PhiBelowLeaf33232 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3323) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childHL phiBelowCell3323)
    e24KC2PhiBelowLeaf33232_c0 e24KC2PhiBelowLeaf33232_c1 e24KC2PhiBelowLeaf33232_c2
      e24KC2PhiBelowLeaf33232_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c0_8_00358
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsef857ed1c7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsef857ed1c7

open CertificateCellsef857ed1c7

theorem e24KC2PhiBelowLeaf33233_c0 :
    adaptiveCoverCheck 8 (childLL (childHH phiBelowCell3323)) = true :=
  adaptiveCoverCheck_succ_of_children 7 (childLL (childHH phiBelowCell3323))
    e24KC2PhiBelowLeaf33233_c0_c0 e24KC2PhiBelowLeaf33233_c0_c1 e24KC2PhiBelowLeaf33233_c0_c2
      e24KC2PhiBelowLeaf33233_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c0_c2_6_00369
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2ebe0c2db9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells2ebe0c2db9

open CertificateCells2ebe0c2db9

theorem e24KC2PhiBelowLeaf33233_c2_c0_c2 :
    adaptiveCoverCheck 6 phiBelowCell33233202 = true :=
  adaptiveCoverCheck_succ_of_children 5 phiBelowCell33233202
    e24KC2PhiBelowLeaf33233_c2_c0_c2_c0 e24KC2PhiBelowLeaf33233_c2_c0_c2_c1
      e24KC2PhiBelowLeaf33233_c2_c0_c2_c2 e24KC2PhiBelowLeaf33233_c2_c0_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c0_7_00371
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells27c0e8c594

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells27c0e8c594

open CertificateCells27c0e8c594

theorem e24KC2PhiBelowLeaf33233_c2_c0 :
    adaptiveCoverCheck 7 (childLL (childHL (childHH phiBelowCell3323))) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childHH phiBelowCell3323)))
    e24KC2PhiBelowLeaf33233_c2_c0_c0 e24KC2PhiBelowLeaf33233_c2_c0_c1
      e24KC2PhiBelowLeaf33233_c2_c0_c2 e24KC2PhiBelowLeaf33233_c2_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_c0_c3_5_00383
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4d117fb26d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells4d117fb26d

open CertificateCells4d117fb26d

theorem e24KC2PhiBelowLeaf33233_c2_c2_c0_c3 :
    adaptiveCoverCheck 5 (childHH phiBelowCell33233220) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childHH phiBelowCell33233220)
    e24KC2PhiBelowLeaf33233_c2_c2_c0_c3_c0 e24KC2PhiBelowLeaf33233_c2_c2_c0_c3_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c0_c3_c2 e24KC2PhiBelowLeaf33233_c2_c2_c0_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_c0_6_00384
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells848f180c5a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells848f180c5a

open CertificateCells848f180c5a

theorem e24KC2PhiBelowLeaf33233_c2_c2_c0 :
    adaptiveCoverCheck 6 phiBelowCell33233220 = true :=
  adaptiveCoverCheck_succ_of_children 5 phiBelowCell33233220
    e24KC2PhiBelowLeaf33233_c2_c2_c0_c0 e24KC2PhiBelowLeaf33233_c2_c2_c0_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c0_c2 e24KC2PhiBelowLeaf33233_c2_c2_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_c1_6_00390
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells090e12bc76

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells090e12bc76

open CertificateCells090e12bc76

theorem e24KC2PhiBelowLeaf33233_c2_c2_c1 :
    adaptiveCoverCheck 6 phiBelowCell33233221 = true :=
  adaptiveCoverCheck_succ_of_children 5 phiBelowCell33233221
    e24KC2PhiBelowLeaf33233_c2_c2_c1_c0 e24KC2PhiBelowLeaf33233_c2_c2_c1_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c1_c2 e24KC2PhiBelowLeaf33233_c2_c2_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_c2_c1_5_00398
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells857be56025

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells857be56025

open CertificateCells857be56025

theorem e24KC2PhiBelowLeaf33233_c2_c2_c2_c1 :
    adaptiveCoverCheck 5 (childLH phiBelowCell33233222) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH phiBelowCell33233222)
    e24KC2PhiBelowLeaf33233_c2_c2_c2_c1_c0 e24KC2PhiBelowLeaf33233_c2_c2_c2_c1_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c2_c1_c2 e24KC2PhiBelowLeaf33233_c2_c2_c2_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_c2_6_00401
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsea76f7562d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsea76f7562d

open CertificateCellsea76f7562d

theorem e24KC2PhiBelowLeaf33233_c2_c2_c2 :
    adaptiveCoverCheck 6 phiBelowCell33233222 = true :=
  adaptiveCoverCheck_succ_of_children 5 phiBelowCell33233222
    e24KC2PhiBelowLeaf33233_c2_c2_c2_c0 e24KC2PhiBelowLeaf33233_c2_c2_c2_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c2_c2 e24KC2PhiBelowLeaf33233_c2_c2_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_c3_c0_5_00408
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsdd77c2320b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsdd77c2320b

open CertificateCellsdd77c2320b

theorem e24KC2PhiBelowLeaf33233_c2_c2_c3_c0 :
    adaptiveCoverCheck 5 (childLL phiBelowCell33233223) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL phiBelowCell33233223)
    e24KC2PhiBelowLeaf33233_c2_c2_c3_c0_c0 e24KC2PhiBelowLeaf33233_c2_c2_c3_c0_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c3_c0_c2 e24KC2PhiBelowLeaf33233_c2_c2_c3_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below
Leaf33233_c2_c2_c3_c2_c1_c2_c0_2_00421
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells08c6706994

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells08c6706994

open CertificateCells08c6706994

theorem e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1_c2_c0 :
    adaptiveCoverCheck 2 phiBelowCell332332232120 = true :=
  adaptiveCoverCheck_succ_of_children 1 phiBelowCell332332232120
    e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1_c2_c0_c0
      e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1_c2_c0_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1_c2_c0_c2
      e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1_c2_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below
Leaf33233_c2_c2_c3_c2_c1_c2_3_00425
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells96d537e773

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells96d537e773

open CertificateCells96d537e773

theorem e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1_c2 :
    adaptiveCoverCheck 3 (childHL (childLH (childHL phiBelowCell33233223))) = true :=
  adaptiveCoverCheck_succ_of_children 2 (childHL (childLH (childHL phiBelowCell33233223)))
    e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1_c2_c0 e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1_c2_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1_c2_c2 e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_c3_c2_c1_4_00427
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0abe1d75a7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells0abe1d75a7

open CertificateCells0abe1d75a7

theorem e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1 :
    adaptiveCoverCheck 4 (childLH (childHL phiBelowCell33233223)) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLH (childHL phiBelowCell33233223))
    e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1_c0 e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1_c2 e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_c3_c2_c3_4_00434
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4849d1c13b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells4849d1c13b

open CertificateCells4849d1c13b

theorem e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c3 :
    adaptiveCoverCheck 4 (childHH (childHL phiBelowCell33233223)) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childHH (childHL phiBelowCell33233223))
    e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c3_c0 e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c3_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c3_c2 e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_c3_c2_5_00435
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf2740dc787

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsf2740dc787

open CertificateCellsf2740dc787

theorem e24KC2PhiBelowLeaf33233_c2_c2_c3_c2 :
    adaptiveCoverCheck 5 (childHL phiBelowCell33233223) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childHL phiBelowCell33233223)
    e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c0 e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c2 e24KC2PhiBelowLeaf33233_c2_c2_c3_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_c3_c3_c2_4_00444
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3f18540de9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells3f18540de9

open CertificateCells3f18540de9

theorem e24KC2PhiBelowLeaf33233_c2_c2_c3_c3_c2 :
    adaptiveCoverCheck 4 (childHL (childHH phiBelowCell33233223)) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childHL (childHH phiBelowCell33233223))
    e24KC2PhiBelowLeaf33233_c2_c2_c3_c3_c2_c0 e24KC2PhiBelowLeaf33233_c2_c2_c3_c3_c2_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c3_c3_c2_c2 e24KC2PhiBelowLeaf33233_c2_c2_c3_c3_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_c3_c3_5_00446
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa21caf16f2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsa21caf16f2

open CertificateCellsa21caf16f2

theorem e24KC2PhiBelowLeaf33233_c2_c2_c3_c3 :
    adaptiveCoverCheck 5 (childHH phiBelowCell33233223) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childHH phiBelowCell33233223)
    e24KC2PhiBelowLeaf33233_c2_c2_c3_c3_c0 e24KC2PhiBelowLeaf33233_c2_c2_c3_c3_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c3_c3_c2 e24KC2PhiBelowLeaf33233_c2_c2_c3_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_c3_6_00447
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells21943a9b83

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells21943a9b83

open CertificateCells21943a9b83

theorem e24KC2PhiBelowLeaf33233_c2_c2_c3 :
    adaptiveCoverCheck 6 phiBelowCell33233223 = true :=
  adaptiveCoverCheck_succ_of_children 5 phiBelowCell33233223
    e24KC2PhiBelowLeaf33233_c2_c2_c3_c0 e24KC2PhiBelowLeaf33233_c2_c2_c3_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c3_c2 e24KC2PhiBelowLeaf33233_c2_c2_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_7_00448
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells62ff50a4e8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells62ff50a4e8

open CertificateCells62ff50a4e8

theorem e24KC2PhiBelowLeaf33233_c2_c2 :
    adaptiveCoverCheck 7 (childHL (childHL (childHH phiBelowCell3323))) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childHH phiBelowCell3323)))
    e24KC2PhiBelowLeaf33233_c2_c2_c0 e24KC2PhiBelowLeaf33233_c2_c2_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c2 e24KC2PhiBelowLeaf33233_c2_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c3_c2_6_00457
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6677fc4b7c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells6677fc4b7c

open CertificateCells6677fc4b7c

theorem e24KC2PhiBelowLeaf33233_c2_c3_c2 :
    adaptiveCoverCheck 6 phiBelowCell33233232 = true :=
  adaptiveCoverCheck_succ_of_children 5 phiBelowCell33233232
    e24KC2PhiBelowLeaf33233_c2_c3_c2_c0 e24KC2PhiBelowLeaf33233_c2_c3_c2_c1
      e24KC2PhiBelowLeaf33233_c2_c3_c2_c2 e24KC2PhiBelowLeaf33233_c2_c3_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c3_7_00459
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells07875eeb47

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells07875eeb47

open CertificateCells07875eeb47

theorem e24KC2PhiBelowLeaf33233_c2_c3 :
    adaptiveCoverCheck 7 (childHH (childHL (childHH phiBelowCell3323))) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childHH phiBelowCell3323)))
    e24KC2PhiBelowLeaf33233_c2_c3_c0 e24KC2PhiBelowLeaf33233_c2_c3_c1
      e24KC2PhiBelowLeaf33233_c2_c3_c2 e24KC2PhiBelowLeaf33233_c2_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_8_00460
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5ed2775b48

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells5ed2775b48

open CertificateCells5ed2775b48

theorem e24KC2PhiBelowLeaf33233_c2 :
    adaptiveCoverCheck 8 (childHL (childHH phiBelowCell3323)) = true :=
  adaptiveCoverCheck_succ_of_children 7 (childHL (childHH phiBelowCell3323))
    e24KC2PhiBelowLeaf33233_c2_c0 e24KC2PhiBelowLeaf33233_c2_c1 e24KC2PhiBelowLeaf33233_c2_c2
      e24KC2PhiBelowLeaf33233_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_9_00462
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells83d9ff7319

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells83d9ff7319

open CertificateCells83d9ff7319

theorem e24KC2PhiBelowLeaf33233 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3323) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childHH phiBelowCell3323)
    e24KC2PhiBelowLeaf33233_c0 e24KC2PhiBelowLeaf33233_c1 e24KC2PhiBelowLeaf33233_c2
      e24KC2PhiBelowLeaf33233_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC6Phi Below Reconstruct
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells240a9bf558

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells240a9bf558

open CertificateCells240a9bf558

theorem e24KC2PhiBelowNode3000 :
    adaptiveCoverCheck 10 phiBelowCell3000 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3000
    e24KC2PhiBelowLeaf30000 e24KC2PhiBelowLeaf30001 e24KC2PhiBelowLeaf30002 e24KC2PhiBelowLeaf30003

theorem e24KC2PhiBelowNode3001 :
    adaptiveCoverCheck 10 phiBelowCell3001 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3001
    e24KC2PhiBelowLeaf30010 e24KC2PhiBelowLeaf30011 e24KC2PhiBelowLeaf30012 e24KC2PhiBelowLeaf30013

theorem e24KC2PhiBelowNode3002 :
    adaptiveCoverCheck 10 phiBelowCell3002 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3002
    e24KC2PhiBelowLeaf30020 e24KC2PhiBelowLeaf30021 e24KC2PhiBelowLeaf30022 e24KC2PhiBelowLeaf30023

theorem e24KC2PhiBelowNode3003 :
    adaptiveCoverCheck 10 phiBelowCell3003 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3003
    e24KC2PhiBelowLeaf30030 e24KC2PhiBelowLeaf30031 e24KC2PhiBelowLeaf30032 e24KC2PhiBelowLeaf30033

theorem e24KC2PhiBelowNode3010 :
    adaptiveCoverCheck 10 phiBelowCell3010 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3010
    e24KC2PhiBelowLeaf30100 e24KC2PhiBelowLeaf30101 e24KC2PhiBelowLeaf30102 e24KC2PhiBelowLeaf30103

theorem e24KC2PhiBelowNode3011 :
    adaptiveCoverCheck 10 phiBelowCell3011 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3011
    e24KC2PhiBelowLeaf30110 e24KC2PhiBelowLeaf30111 e24KC2PhiBelowLeaf30112 e24KC2PhiBelowLeaf30113

theorem e24KC2PhiBelowNode3012 :
    adaptiveCoverCheck 10 phiBelowCell3012 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3012
    e24KC2PhiBelowLeaf30120 e24KC2PhiBelowLeaf30121 e24KC2PhiBelowLeaf30122 e24KC2PhiBelowLeaf30123

theorem e24KC2PhiBelowNode3013 :
    adaptiveCoverCheck 10 phiBelowCell3013 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3013
    e24KC2PhiBelowLeaf30130 e24KC2PhiBelowLeaf30131 e24KC2PhiBelowLeaf30132 e24KC2PhiBelowLeaf30133

theorem e24KC2PhiBelowNode3020 :
    adaptiveCoverCheck 10 phiBelowCell3020 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3020
    e24KC2PhiBelowLeaf30200 e24KC2PhiBelowLeaf30201 e24KC2PhiBelowLeaf30202 e24KC2PhiBelowLeaf30203

theorem e24KC2PhiBelowNode3021 :
    adaptiveCoverCheck 10 phiBelowCell3021 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3021
    e24KC2PhiBelowLeaf30210 e24KC2PhiBelowLeaf30211 e24KC2PhiBelowLeaf30212 e24KC2PhiBelowLeaf30213

theorem e24KC2PhiBelowNode3022 :
    adaptiveCoverCheck 10 phiBelowCell3022 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3022
    e24KC2PhiBelowLeaf30220 e24KC2PhiBelowLeaf30221 e24KC2PhiBelowLeaf30222 e24KC2PhiBelowLeaf30223

theorem e24KC2PhiBelowNode3023 :
    adaptiveCoverCheck 10 phiBelowCell3023 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3023
    e24KC2PhiBelowLeaf30230 e24KC2PhiBelowLeaf30231 e24KC2PhiBelowLeaf30232 e24KC2PhiBelowLeaf30233

theorem e24KC2PhiBelowNode3030 :
    adaptiveCoverCheck 10 phiBelowCell3030 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3030
    e24KC2PhiBelowLeaf30300 e24KC2PhiBelowLeaf30301 e24KC2PhiBelowLeaf30302 e24KC2PhiBelowLeaf30303

theorem e24KC2PhiBelowNode3031 :
    adaptiveCoverCheck 10 phiBelowCell3031 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3031
    e24KC2PhiBelowLeaf30310 e24KC2PhiBelowLeaf30311 e24KC2PhiBelowLeaf30312 e24KC2PhiBelowLeaf30313

theorem e24KC2PhiBelowNode3032 :
    adaptiveCoverCheck 10 phiBelowCell3032 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3032
    e24KC2PhiBelowLeaf30320 e24KC2PhiBelowLeaf30321 e24KC2PhiBelowLeaf30322 e24KC2PhiBelowLeaf30323

theorem e24KC2PhiBelowNode3033 :
    adaptiveCoverCheck 10 phiBelowCell3033 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3033
    e24KC2PhiBelowLeaf30330 e24KC2PhiBelowLeaf30331 e24KC2PhiBelowLeaf30332 e24KC2PhiBelowLeaf30333

theorem e24KC2PhiBelowNode3100 :
    adaptiveCoverCheck 10 phiBelowCell3100 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3100
    e24KC2PhiBelowLeaf31000 e24KC2PhiBelowLeaf31001 e24KC2PhiBelowLeaf31002 e24KC2PhiBelowLeaf31003

theorem e24KC2PhiBelowNode3101 :
    adaptiveCoverCheck 10 phiBelowCell3101 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3101
    e24KC2PhiBelowLeaf31010 e24KC2PhiBelowLeaf31011 e24KC2PhiBelowLeaf31012 e24KC2PhiBelowLeaf31013

theorem e24KC2PhiBelowNode3102 :
    adaptiveCoverCheck 10 phiBelowCell3102 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3102
    e24KC2PhiBelowLeaf31020 e24KC2PhiBelowLeaf31021 e24KC2PhiBelowLeaf31022 e24KC2PhiBelowLeaf31023

theorem e24KC2PhiBelowNode3103 :
    adaptiveCoverCheck 10 phiBelowCell3103 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3103
    e24KC2PhiBelowLeaf31030 e24KC2PhiBelowLeaf31031 e24KC2PhiBelowLeaf31032 e24KC2PhiBelowLeaf31033

theorem e24KC2PhiBelowNode3112 :
    adaptiveCoverCheck 10 phiBelowCell3112 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3112
    e24KC2PhiBelowLeaf31120 e24KC2PhiBelowLeaf31121 e24KC2PhiBelowLeaf31122 e24KC2PhiBelowLeaf31123

theorem e24KC2PhiBelowNode3120 :
    adaptiveCoverCheck 10 phiBelowCell3120 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3120
    e24KC2PhiBelowLeaf31200 e24KC2PhiBelowLeaf31201 e24KC2PhiBelowLeaf31202 e24KC2PhiBelowLeaf31203

theorem e24KC2PhiBelowNode3121 :
    adaptiveCoverCheck 10 phiBelowCell3121 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3121
    e24KC2PhiBelowLeaf31210 e24KC2PhiBelowLeaf31211 e24KC2PhiBelowLeaf31212 e24KC2PhiBelowLeaf31213

theorem e24KC2PhiBelowNode3122 :
    adaptiveCoverCheck 10 phiBelowCell3122 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3122
    e24KC2PhiBelowLeaf31220 e24KC2PhiBelowLeaf31221 e24KC2PhiBelowLeaf31222 e24KC2PhiBelowLeaf31223

theorem e24KC2PhiBelowNode3123 :
    adaptiveCoverCheck 10 phiBelowCell3123 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3123
    e24KC2PhiBelowLeaf31230 e24KC2PhiBelowLeaf31231 e24KC2PhiBelowLeaf31232 e24KC2PhiBelowLeaf31233

theorem e24KC2PhiBelowNode3130 :
    adaptiveCoverCheck 10 phiBelowCell3130 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3130
    e24KC2PhiBelowLeaf31300 e24KC2PhiBelowLeaf31301 e24KC2PhiBelowLeaf31302 e24KC2PhiBelowLeaf31303

theorem e24KC2PhiBelowNode3131 :
    adaptiveCoverCheck 10 phiBelowCell3131 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3131
    e24KC2PhiBelowLeaf31310 e24KC2PhiBelowLeaf31311 e24KC2PhiBelowLeaf31312 e24KC2PhiBelowLeaf31313

theorem e24KC2PhiBelowNode3132 :
    adaptiveCoverCheck 10 phiBelowCell3132 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3132
    e24KC2PhiBelowLeaf31320 e24KC2PhiBelowLeaf31321 e24KC2PhiBelowLeaf31322 e24KC2PhiBelowLeaf31323

theorem e24KC2PhiBelowNode3133 :
    adaptiveCoverCheck 10 phiBelowCell3133 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3133
    e24KC2PhiBelowLeaf31330 e24KC2PhiBelowLeaf31331 e24KC2PhiBelowLeaf31332 e24KC2PhiBelowLeaf31333

theorem e24KC2PhiBelowNode3200 :
    adaptiveCoverCheck 10 phiBelowCell3200 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3200
    e24KC2PhiBelowLeaf32000 e24KC2PhiBelowLeaf32001 e24KC2PhiBelowLeaf32002 e24KC2PhiBelowLeaf32003

theorem e24KC2PhiBelowNode3201 :
    adaptiveCoverCheck 10 phiBelowCell3201 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3201
    e24KC2PhiBelowLeaf32010 e24KC2PhiBelowLeaf32011 e24KC2PhiBelowLeaf32012 e24KC2PhiBelowLeaf32013

theorem e24KC2PhiBelowNode3202 :
    adaptiveCoverCheck 10 phiBelowCell3202 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3202
    e24KC2PhiBelowLeaf32020 e24KC2PhiBelowLeaf32021 e24KC2PhiBelowLeaf32022 e24KC2PhiBelowLeaf32023

theorem e24KC2PhiBelowNode3203 :
    adaptiveCoverCheck 10 phiBelowCell3203 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3203
    e24KC2PhiBelowLeaf32030 e24KC2PhiBelowLeaf32031 e24KC2PhiBelowLeaf32032 e24KC2PhiBelowLeaf32033

theorem e24KC2PhiBelowNode3210 :
    adaptiveCoverCheck 10 phiBelowCell3210 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3210
    e24KC2PhiBelowLeaf32100 e24KC2PhiBelowLeaf32101 e24KC2PhiBelowLeaf32102 e24KC2PhiBelowLeaf32103

theorem e24KC2PhiBelowNode3211 :
    adaptiveCoverCheck 10 phiBelowCell3211 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3211
    e24KC2PhiBelowLeaf32110 e24KC2PhiBelowLeaf32111 e24KC2PhiBelowLeaf32112 e24KC2PhiBelowLeaf32113

theorem e24KC2PhiBelowNode3212 :
    adaptiveCoverCheck 10 phiBelowCell3212 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3212
    e24KC2PhiBelowLeaf32120 e24KC2PhiBelowLeaf32121 e24KC2PhiBelowLeaf32122 e24KC2PhiBelowLeaf32123

theorem e24KC2PhiBelowNode3213 :
    adaptiveCoverCheck 10 phiBelowCell3213 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3213
    e24KC2PhiBelowLeaf32130 e24KC2PhiBelowLeaf32131 e24KC2PhiBelowLeaf32132 e24KC2PhiBelowLeaf32133

theorem e24KC2PhiBelowNode3220 :
    adaptiveCoverCheck 10 phiBelowCell3220 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3220
    e24KC2PhiBelowLeaf32200 e24KC2PhiBelowLeaf32201 e24KC2PhiBelowLeaf32202 e24KC2PhiBelowLeaf32203

theorem e24KC2PhiBelowNode3221 :
    adaptiveCoverCheck 10 phiBelowCell3221 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3221
    e24KC2PhiBelowLeaf32210 e24KC2PhiBelowLeaf32211 e24KC2PhiBelowLeaf32212 e24KC2PhiBelowLeaf32213

theorem e24KC2PhiBelowNode3222 :
    adaptiveCoverCheck 10 phiBelowCell3222 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3222
    e24KC2PhiBelowLeaf32220 e24KC2PhiBelowLeaf32221 e24KC2PhiBelowLeaf32222 e24KC2PhiBelowLeaf32223

theorem e24KC2PhiBelowNode3223 :
    adaptiveCoverCheck 10 phiBelowCell3223 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3223
    e24KC2PhiBelowLeaf32230 e24KC2PhiBelowLeaf32231 e24KC2PhiBelowLeaf32232 e24KC2PhiBelowLeaf32233

theorem e24KC2PhiBelowNode3230 :
    adaptiveCoverCheck 10 phiBelowCell3230 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3230
    e24KC2PhiBelowLeaf32300 e24KC2PhiBelowLeaf32301 e24KC2PhiBelowLeaf32302 e24KC2PhiBelowLeaf32303

theorem e24KC2PhiBelowNode3231 :
    adaptiveCoverCheck 10 phiBelowCell3231 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3231
    e24KC2PhiBelowLeaf32310 e24KC2PhiBelowLeaf32311 e24KC2PhiBelowLeaf32312 e24KC2PhiBelowLeaf32313

theorem e24KC2PhiBelowNode3232 :
    adaptiveCoverCheck 10 phiBelowCell3232 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3232
    e24KC2PhiBelowLeaf32320 e24KC2PhiBelowLeaf32321 e24KC2PhiBelowLeaf32322 e24KC2PhiBelowLeaf32323

theorem e24KC2PhiBelowNode3233 :
    adaptiveCoverCheck 10 phiBelowCell3233 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3233
    e24KC2PhiBelowLeaf32330 e24KC2PhiBelowLeaf32331 e24KC2PhiBelowLeaf32332 e24KC2PhiBelowLeaf32333

theorem e24KC2PhiBelowNode3300 :
    adaptiveCoverCheck 10 phiBelowCell3300 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3300
    e24KC2PhiBelowLeaf33000 e24KC2PhiBelowLeaf33001 e24KC2PhiBelowLeaf33002 e24KC2PhiBelowLeaf33003

theorem e24KC2PhiBelowNode3301 :
    adaptiveCoverCheck 10 phiBelowCell3301 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3301
    e24KC2PhiBelowLeaf33010 e24KC2PhiBelowLeaf33011 e24KC2PhiBelowLeaf33012 e24KC2PhiBelowLeaf33013

theorem e24KC2PhiBelowNode3302 :
    adaptiveCoverCheck 10 phiBelowCell3302 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3302
    e24KC2PhiBelowLeaf33020 e24KC2PhiBelowLeaf33021 e24KC2PhiBelowLeaf33022 e24KC2PhiBelowLeaf33023

theorem e24KC2PhiBelowNode3303 :
    adaptiveCoverCheck 10 phiBelowCell3303 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3303
    e24KC2PhiBelowLeaf33030 e24KC2PhiBelowLeaf33031 e24KC2PhiBelowLeaf33032 e24KC2PhiBelowLeaf33033

theorem e24KC2PhiBelowNode3310 :
    adaptiveCoverCheck 10 phiBelowCell3310 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3310
    e24KC2PhiBelowLeaf33100 e24KC2PhiBelowLeaf33101 e24KC2PhiBelowLeaf33102 e24KC2PhiBelowLeaf33103

theorem e24KC2PhiBelowNode3311 :
    adaptiveCoverCheck 10 phiBelowCell3311 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3311
    e24KC2PhiBelowLeaf33110 e24KC2PhiBelowLeaf33111 e24KC2PhiBelowLeaf33112 e24KC2PhiBelowLeaf33113

theorem e24KC2PhiBelowNode3312 :
    adaptiveCoverCheck 10 phiBelowCell3312 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3312
    e24KC2PhiBelowLeaf33120 e24KC2PhiBelowLeaf33121 e24KC2PhiBelowLeaf33122 e24KC2PhiBelowLeaf33123

theorem e24KC2PhiBelowNode3313 :
    adaptiveCoverCheck 10 phiBelowCell3313 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3313
    e24KC2PhiBelowLeaf33130 e24KC2PhiBelowLeaf33131 e24KC2PhiBelowLeaf33132 e24KC2PhiBelowLeaf33133

theorem e24KC2PhiBelowNode3320 :
    adaptiveCoverCheck 10 phiBelowCell3320 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3320
    e24KC2PhiBelowLeaf33200 e24KC2PhiBelowLeaf33201 e24KC2PhiBelowLeaf33202 e24KC2PhiBelowLeaf33203

theorem e24KC2PhiBelowNode3321 :
    adaptiveCoverCheck 10 phiBelowCell3321 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3321
    e24KC2PhiBelowLeaf33210 e24KC2PhiBelowLeaf33211 e24KC2PhiBelowLeaf33212 e24KC2PhiBelowLeaf33213

theorem e24KC2PhiBelowNode3322 :
    adaptiveCoverCheck 10 phiBelowCell3322 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3322
    e24KC2PhiBelowLeaf33220 e24KC2PhiBelowLeaf33221 e24KC2PhiBelowLeaf33222 e24KC2PhiBelowLeaf33223

theorem e24KC2PhiBelowNode3323 :
    adaptiveCoverCheck 10 phiBelowCell3323 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3323
    e24KC2PhiBelowLeaf33230 e24KC2PhiBelowLeaf33231 e24KC2PhiBelowLeaf33232 e24KC2PhiBelowLeaf33233

theorem e24KC2PhiBelowNode3330 :
    adaptiveCoverCheck 10 phiBelowCell3330 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3330
    e24KC2PhiBelowLeaf33300 e24KC2PhiBelowLeaf33301 e24KC2PhiBelowLeaf33302 e24KC2PhiBelowLeaf33303

theorem e24KC2PhiBelowNode3331 :
    adaptiveCoverCheck 10 phiBelowCell3331 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3331
    e24KC2PhiBelowLeaf33310 e24KC2PhiBelowLeaf33311 e24KC2PhiBelowLeaf33312 e24KC2PhiBelowLeaf33313

theorem e24KC2PhiBelowNode3332 :
    adaptiveCoverCheck 10 phiBelowCell3332 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3332
    e24KC2PhiBelowLeaf33320 e24KC2PhiBelowLeaf33321 e24KC2PhiBelowLeaf33322 e24KC2PhiBelowLeaf33323

theorem e24KC2PhiBelowNode3333 :
    adaptiveCoverCheck 10 phiBelowCell3333 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3333
    e24KC2PhiBelowLeaf33330 e24KC2PhiBelowLeaf33331 e24KC2PhiBelowLeaf33332 e24KC2PhiBelowLeaf33333

theorem e24KC2PhiBelowNode300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3000 e24KC2PhiBelowNode3001 e24KC2PhiBelowNode3002 e24KC2PhiBelowNode3003

theorem e24KC2PhiBelowNode301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3010 e24KC2PhiBelowNode3011 e24KC2PhiBelowNode3012 e24KC2PhiBelowNode3013

theorem e24KC2PhiBelowNode302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3020 e24KC2PhiBelowNode3021 e24KC2PhiBelowNode3022 e24KC2PhiBelowNode3023

theorem e24KC2PhiBelowNode303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3030 e24KC2PhiBelowNode3031 e24KC2PhiBelowNode3032 e24KC2PhiBelowNode3033

theorem e24KC2PhiBelowNode310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3100 e24KC2PhiBelowNode3101 e24KC2PhiBelowNode3102 e24KC2PhiBelowNode3103

theorem e24KC2PhiBelowNode311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowLeaf3110 e24KC2PhiBelowLeaf3111 e24KC2PhiBelowNode3112 e24KC2PhiBelowLeaf3113

theorem e24KC2PhiBelowNode312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3120 e24KC2PhiBelowNode3121 e24KC2PhiBelowNode3122 e24KC2PhiBelowNode3123

theorem e24KC2PhiBelowNode313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3130 e24KC2PhiBelowNode3131 e24KC2PhiBelowNode3132 e24KC2PhiBelowNode3133

theorem e24KC2PhiBelowNode320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3200 e24KC2PhiBelowNode3201 e24KC2PhiBelowNode3202 e24KC2PhiBelowNode3203

theorem e24KC2PhiBelowNode321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3210 e24KC2PhiBelowNode3211 e24KC2PhiBelowNode3212 e24KC2PhiBelowNode3213

theorem e24KC2PhiBelowNode322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3220 e24KC2PhiBelowNode3221 e24KC2PhiBelowNode3222 e24KC2PhiBelowNode3223

theorem e24KC2PhiBelowNode323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3230 e24KC2PhiBelowNode3231 e24KC2PhiBelowNode3232 e24KC2PhiBelowNode3233

theorem e24KC2PhiBelowNode330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3300 e24KC2PhiBelowNode3301 e24KC2PhiBelowNode3302 e24KC2PhiBelowNode3303

theorem e24KC2PhiBelowNode331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3310 e24KC2PhiBelowNode3311 e24KC2PhiBelowNode3312 e24KC2PhiBelowNode3313

theorem e24KC2PhiBelowNode332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3320 e24KC2PhiBelowNode3321 e24KC2PhiBelowNode3322 e24KC2PhiBelowNode3323

theorem e24KC2PhiBelowNode333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3330 e24KC2PhiBelowNode3331 e24KC2PhiBelowNode3332 e24KC2PhiBelowNode3333

theorem e24KC2PhiBelowNode30 :
    adaptiveCoverCheck 12 (childLL (childHH e24PhiBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH e24PhiBelowRoot))
    e24KC2PhiBelowNode300 e24KC2PhiBelowNode301 e24KC2PhiBelowNode302 e24KC2PhiBelowNode303

theorem e24KC2PhiBelowNode31 :
    adaptiveCoverCheck 12 (childLH (childHH e24PhiBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH e24PhiBelowRoot))
    e24KC2PhiBelowNode310 e24KC2PhiBelowNode311 e24KC2PhiBelowNode312 e24KC2PhiBelowNode313

theorem e24KC2PhiBelowNode32 :
    adaptiveCoverCheck 12 (childHL (childHH e24PhiBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH e24PhiBelowRoot))
    e24KC2PhiBelowNode320 e24KC2PhiBelowNode321 e24KC2PhiBelowNode322 e24KC2PhiBelowNode323

theorem e24KC2PhiBelowNode33 :
    adaptiveCoverCheck 12 (childHH (childHH e24PhiBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH e24PhiBelowRoot))
    e24KC2PhiBelowNode330 e24KC2PhiBelowNode331 e24KC2PhiBelowNode332 e24KC2PhiBelowNode333

theorem e24KC2PhiBelowNode3 :
    adaptiveCoverCheck 13 (childHH e24PhiBelowRoot) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH e24PhiBelowRoot)
    e24KC2PhiBelowNode30 e24KC2PhiBelowNode31 e24KC2PhiBelowNode32 e24KC2PhiBelowNode33

theorem e24KC2PhiBelowNodeROOT :
    adaptiveCoverCheck 14 e24PhiBelowRoot = true :=
  adaptiveCoverCheck_succ_of_children 13 e24PhiBelowRoot
    e24PhiBelowKernelLL e24PhiBelowKernelLH e24PhiBelowKernelHL e24KC2PhiBelowNode3

theorem e24PhiBelowKernelCheck :
    adaptiveCoverCheck 14 e24PhiBelowRoot = true :=
  e24KC2PhiBelowNodeROOT

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_c2_4_00016
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells22695df69a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells22695df69a

open CertificateCells22695df69a

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022002011))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH thetaAboveCell000022002011)))
    e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2_c0
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2_c2
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_c3_4_00022
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells782ac45202

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells782ac45202

open CertificateCells782ac45202

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3 :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022002011))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH thetaAboveCell000022002011)))
    e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3_c0
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3_c2
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_5_00023
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb8f48433cf

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsb8f48433cf

open CertificateCellsb8f48433cf

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022002011)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022002011))
    e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c0 e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2 e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_c0_4_00484
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5bc1aa1a31

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells5bc1aa1a31

open CertificateCells5bc1aa1a31

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0 :
    adaptiveCoverCheck 4 (childLL (childLL (childHL thetaAboveCell000022002000))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL thetaAboveCell000022002000)))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0_c0
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0_c2
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_c1_4_00490
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells29b43c6eb7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells29b43c6eb7

open CertificateCells29b43c6eb7

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1 :
    adaptiveCoverCheck 4 (childLH (childLL (childHL thetaAboveCell000022002000))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL thetaAboveCell000022002000)))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1_c0
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1_c2
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_5_00493
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells64bf70ad53

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells64bf70ad53

open CertificateCells64bf70ad53

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022002000)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022002000))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0 e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c2 e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c1_c0_4_00500
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc935d550f9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsc935d550f9

open CertificateCellsc935d550f9

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c0 :
    adaptiveCoverCheck 4 (childLL (childLH (childHL thetaAboveCell000022002000))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL thetaAboveCell000022002000)))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c0_c0
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c0_c2
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c1_c1_4_00506
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0a80d69c2b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells0a80d69c2b

open CertificateCells0a80d69c2b

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c1 :
    adaptiveCoverCheck 4 (childLH (childLH (childHL thetaAboveCell000022002000))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHL thetaAboveCell000022002000)))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c1_c0
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c1_c2
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c1_5_00509
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsfd35b16333

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsfd35b16333

open CertificateCellsfd35b16333

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022002000)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022002000))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c0 e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c2 e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c0_c0_c2_6_00512
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd8bbac8cc5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsd8bbac8cc5

open CertificateCellsd8bbac8cc5

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022002000) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022002000)
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0 e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c2 e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c0_c0_4_00520
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2eb3bc7e90

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells2eb3bc7e90

open CertificateCells2eb3bc7e90

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c0 :
    adaptiveCoverCheck 4 (childLL (childLL (childHH thetaAboveCell000022002000))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHH thetaAboveCell000022002000)))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c0_c0
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c0_c2
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c0_c1_4_00526
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsbc99de789e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsbc99de789e

open CertificateCellsbc99de789e

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c1 :
    adaptiveCoverCheck 4 (childLH (childLL (childHH thetaAboveCell000022002000))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHH thetaAboveCell000022002000)))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c1_c0
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c1_c2
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c0_5_00529
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsdc52d78b64

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsdc52d78b64

open CertificateCellsdc52d78b64

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022002000)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022002000))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c0 e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c2 e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c1_c0_4_00536
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells69f98d6dd4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells69f98d6dd4

open CertificateCells69f98d6dd4

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c0 :
    adaptiveCoverCheck 4 (childLL (childLH (childHH thetaAboveCell000022002000))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHH thetaAboveCell000022002000)))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c0_c0
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c0_c2
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c1_c1_4_00542
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells675835e7b9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells675835e7b9

open CertificateCells675835e7b9

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c1 :
    adaptiveCoverCheck 4 (childLH (childLH (childHH thetaAboveCell000022002000))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHH thetaAboveCell000022002000)))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c1_c0
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c1_c2
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c1_5_00545
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsda5cde5aa9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsda5cde5aa9

open CertificateCellsda5cde5aa9

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022002000)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022002000))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c0 e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c2 e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c0_c0_c3_6_00548
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsed33eab041

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsed33eab041

open CertificateCellsed33eab041

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022002000) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022002000)
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0 e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c2 e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c0_c0_7_00549
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf997ca54bf

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsf997ca54bf

open CertificateCellsf997ca54bf

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0 :
    adaptiveCoverCheck 7 thetaAboveCell000022002000 = true :=
  adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022002000
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c0 e24KC2ThetaAboveLeaf0000220020_c0_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2 e24KC2ThetaAboveLeaf0000220020_c0_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_c0_4_00560
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsba35077fe5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsba35077fe5

open CertificateCellsba35077fe5

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c0 :
    adaptiveCoverCheck 4 (childLL (childLL (childHL thetaAboveCell000022002001))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL thetaAboveCell000022002001)))
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c0_c0
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c0_c2
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_c1_4_00566
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5d0bfdcc89

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells5d0bfdcc89

open CertificateCells5d0bfdcc89

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c1 :
    adaptiveCoverCheck 4 (childLH (childLL (childHL thetaAboveCell000022002001))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL thetaAboveCell000022002001)))
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c1_c0
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c1_c2
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_5_00569
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb9eba9ae01

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsb9eba9ae01

open CertificateCellsb9eba9ae01

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022002001)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022002001))
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c2 e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c0_4_00576
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5ae8bbaf2e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells5ae8bbaf2e

open CertificateCells5ae8bbaf2e

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0 :
    adaptiveCoverCheck 4 (childLL (childLH (childHL thetaAboveCell000022002001))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL thetaAboveCell000022002001)))
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c0
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c2
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_5_00580
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsbec28e0304

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsbec28e0304

open CertificateCellsbec28e0304

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022002001)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022002001))
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c2 e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c0_c1_c2_6_00583
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1b578c3d10

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells1b578c3d10

open CertificateCells1b578c3d10

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022002001) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022002001)
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c2 e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c0_5_00590
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2bc65b7190

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells2bc65b7190

open CertificateCells2bc65b7190

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022002001)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022002001))
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c2 e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c1_5_00596
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc46dbfc77b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsc46dbfc77b

open CertificateCellsc46dbfc77b

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022002001)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022002001))
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c2 e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c0_c1_c3_6_00599
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells752b604750

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells752b604750

open CertificateCells752b604750

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022002001) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022002001)
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c2 e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c0_c1_7_00600
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse66f3ce3f5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse66f3ce3f5

open CertificateCellse66f3ce3f5

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1 :
    adaptiveCoverCheck 7 thetaAboveCell000022002001 = true :=
  adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022002001
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2 e24KC2ThetaAboveLeaf0000220020_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c0_8_00603
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells45a373af38

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells45a373af38

open CertificateCells45a373af38

theorem e24KC2ThetaAboveLeaf0000220020_c0 :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00002200))) = true :=
  adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00002200)))
    e24KC2ThetaAboveLeaf0000220020_c0_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c2 e24KC2ThetaAboveLeaf0000220020_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c0_5_00614
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsdabf824b24

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsdabf824b24

open CertificateCellsdabf824b24

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022002010)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022002010))
    e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c0 e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c2 e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c1_5_00620
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells11c2c46ea8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells11c2c46ea8

open CertificateCells11c2c46ea8

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022002010)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022002010))
    e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c0 e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c2 e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c1_c0_c2_6_00623
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsfc2738963a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsfc2738963a

open CertificateCellsfc2738963a

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022002010) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022002010)
    e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0 e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c2 e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c0_5_00630
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2c3b2a68a2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells2c3b2a68a2

open CertificateCells2c3b2a68a2

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022002010)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022002010))
    e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c0 e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c2 e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c1_5_00636
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells024fe9d391

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells024fe9d391

open CertificateCells024fe9d391

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022002010)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022002010))
    e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c0 e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c2 e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c1_c0_c3_6_00639
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells95bf7ab700

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells95bf7ab700

open CertificateCells95bf7ab700

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022002010) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022002010)
    e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0 e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c2 e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c1_c0_7_00640
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb2f77f238f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsb2f77f238f

open CertificateCellsb2f77f238f

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0 :
    adaptiveCoverCheck 7 thetaAboveCell000022002010 = true :=
  adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022002010
    e24KC2ThetaAboveLeaf0000220020_c1_c0_c0 e24KC2ThetaAboveLeaf0000220020_c1_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c0_c2 e24KC2ThetaAboveLeaf0000220020_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c1_c2_c0_5_00650
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells8179cb7dd8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells8179cb7dd8

open CertificateCells8179cb7dd8

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c0 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022002011)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022002011))
    e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c0_c0 e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c0_c2 e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c1_c2_c1_5_00656
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsdb257f0c7c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsdb257f0c7c

open CertificateCellsdb257f0c7c

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c1 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022002011)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022002011))
    e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c1_c0 e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c1_c2 e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c1_c1_c2_6_00659
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3a304b7358

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells3a304b7358

open CertificateCells3a304b7358

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c2 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022002011) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022002011)
    e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c0 e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c2 e24KC2ThetaAboveLeaf0000220020_c1_c1_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c0_5_00666
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6cdc8e3bc2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells6cdc8e3bc2

open CertificateCells6cdc8e3bc2

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c0 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022002011)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022002011))
    e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c0_c0 e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c0_c2 e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c1_c1_c3_6_00026
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0157659d62

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells0157659d62

open CertificateCells0157659d62

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022002011) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022002011)
    e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c0 e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c2 e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c1_c1_7_00027
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells834e9932ec

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells834e9932ec

open CertificateCells834e9932ec

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1 :
    adaptiveCoverCheck 7 thetaAboveCell000022002011 = true :=
  adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022002011
    e24KC2ThetaAboveLeaf0000220020_c1_c1_c0 e24KC2ThetaAboveLeaf0000220020_c1_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c2 e24KC2ThetaAboveLeaf0000220020_c1_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-! E24KC6 explicit proof-producing certificate batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb02c7d0e39

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsb02c7d0e39

open CertificateCellsb02c7d0e39
theorem e24KC2ThetaAboveLeaf0000220020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00002200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00002200))
    (by
      exact e24KC2ThetaAboveLeaf0000220020_c0)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL
        thetaAboveCell00002200)))
        (by
          exact e24KC2ThetaAboveLeaf0000220020_c1_c0)
        (by
          exact e24KC2ThetaAboveLeaf0000220020_c1_c1)
        (by
          exact e24KC2ThetaAboveLeaf0000220020_c1_c2)
        (by
          exact e24KC2ThetaAboveLeaf0000220020_c1_c3))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00002200)))
        (by
          have h : (thetaAboveCell000022002020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002020 h)
        (by
          have h : (thetaAboveCell000022002021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002021 h)
        (by
          have h : (thetaAboveCell000022002022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002022 h)
        (by
          have h : (thetaAboveCell000022002023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00002200)))
        (by
          have h : (thetaAboveCell000022002030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002030 h)
        (by
          have h : (thetaAboveCell000022002031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002031 h)
        (by
          have h : (thetaAboveCell000022002032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002032 h)
        (by
          have h : (thetaAboveCell000022002033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002033 h))

end PartE
end GerverSofa

end

end

end

end

end

end
