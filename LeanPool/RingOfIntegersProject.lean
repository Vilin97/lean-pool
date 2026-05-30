/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.AlgebraAuxiliaryLemmas
import LeanPool.RingOfIntegersProject.BrillhartIrreducibilityTest
import LeanPool.RingOfIntegersProject.CertificateDedekind
import LeanPool.RingOfIntegersProject.CertifyAdjoinRoot
import LeanPool.RingOfIntegersProject.CertifyKernel
import LeanPool.RingOfIntegersProject.CertifyMaximality
import LeanPool.RingOfIntegersProject.DedekindCriteria
import LeanPool.RingOfIntegersProject.DegreeLT
import LeanPool.RingOfIntegersProject.Discriminant
import LeanPool.RingOfIntegersProject.DiscriminantSubalgebraBuilder
import LeanPool.RingOfIntegersProject.Homogeneous
import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import LeanPool.RingOfIntegersProject.LinearAlgebraAuxiliaryLemmas
import LeanPool.RingOfIntegersProject.MaximalAPI
import LeanPool.RingOfIntegersProject.PolynomialAsVec
import LeanPool.RingOfIntegersProject.PolynomialBasics
import LeanPool.RingOfIntegersProject.PolynomialRadical
import LeanPool.RingOfIntegersProject.PolynomialsAsLists
import LeanPool.RingOfIntegersProject.QuotientModules
import LeanPool.RingOfIntegersProject.Resultant
import LeanPool.RingOfIntegersProject.Semilinear
import LeanPool.RingOfIntegersProject.SylvesterMatrix
import LeanPool.RingOfIntegersProject.TimesTable.Defs
import LeanPool.RingOfIntegersProject.TimesTableAsLists

/-!
# Certifying rings of integers in number fields

Source: url:https://github.com/alainchmt/RingOfIntegersProject
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
Status: verified
Main declarations: `pMaximal_of_MaximalOrderCertificateLists`, `pMaximal_of_MaximalOrderCertificateOfUnramifiedLists`
Tags: algebraic-number-theory, rings-of-integers, number-fields, formal-verification
MSC: 11R04, 11Y40
-/
