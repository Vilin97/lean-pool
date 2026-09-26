/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/
module


public import LeanPool.InflationTermination.PalomarSolutions.TriangleInflation
public import LeanPool.InflationTermination.PalomarSolutions.TriangleInflationClassification
public import LeanPool.InflationTermination.TriangleInflation
public import LeanPool.InflationTermination.TriangleInflation.ConvexOrder
public import LeanPool.InflationTermination.TriangleInflation.Defect
public import LeanPool.InflationTermination.TriangleInflation.DefectLaw
public import LeanPool.InflationTermination.TriangleInflation.Defs
public import LeanPool.InflationTermination.TriangleInflation.Exponent
public import LeanPool.InflationTermination.TriangleInflation.Fan
public import LeanPool.InflationTermination.TriangleInflation.FiniteWeights
public import LeanPool.InflationTermination.TriangleInflation.Finner
public import LeanPool.InflationTermination.TriangleInflation.FinnerMeasure
public import LeanPool.InflationTermination.TriangleInflation.Graph
public import LeanPool.InflationTermination.TriangleInflation.Graph.Classification
public import LeanPool.InflationTermination.TriangleInflation.Graph.ClassificationTheorem
public import LeanPool.InflationTermination.TriangleInflation.Graph.CycleObstruction
public import LeanPool.InflationTermination.TriangleInflation.Graph.CycleWitness
public import LeanPool.InflationTermination.TriangleInflation.Graph.Cycles
public import LeanPool.InflationTermination.TriangleInflation.Graph.Defs
public import LeanPool.InflationTermination.TriangleInflation.Graph.DoubleStar
public import LeanPool.InflationTermination.TriangleInflation.Graph.DoubleStarForest
public import LeanPool.InflationTermination.TriangleInflation.Graph.FivePath
public import LeanPool.InflationTermination.TriangleInflation.Graph.FivePathWitness
public import LeanPool.InflationTermination.TriangleInflation.Graph.Flips
public import LeanPool.InflationTermination.TriangleInflation.Graph.Linear
public import LeanPool.InflationTermination.TriangleInflation.Graph.RootSink
public import LeanPool.InflationTermination.TriangleInflation.Graph.Soundness
public import LeanPool.InflationTermination.TriangleInflation.Graph.SquareWitness
public import LeanPool.InflationTermination.TriangleInflation.Graph.Transport
public import LeanPool.InflationTermination.TriangleInflation.Graph.Triangle
public import LeanPool.InflationTermination.TriangleInflation.Graph.TriangleWitness
public import LeanPool.InflationTermination.TriangleInflation.Main
public import LeanPool.InflationTermination.TriangleInflation.Rate

/-!
# Inflation termination for classical pair-source networks

Source: url:https://github.com/williamjblair/inflation-termination
Authors: William Blair
Status: verified
Main declarations: `TriangleInflation.Graph.classification_NW`
Tags: causal-inference, probability, inflation-hierarchy, graph-theory
MSC: 60A05, 05C05
-/

/-
Upstream MIT license notice (retained for the Apache 2.0 port):

MIT License

Copyright (c) 2026 William Blair

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
