/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

Adaptation: project module paths and explicit public imports.
Upstream: https://github.com/LeanPool/lean-pool/blob/86da5902e640ceb44e53f88c4a04f870dc062126/LeanPool/Rado/Main.lean
Original source SHA256: 6402a12d160bbdc4a7e5463460ecfb4b5b7aec6f677aaf48295a37894c27d9c5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import LowDimensionalTopology.External.LeanPool.Rado.Surface.Assembly
public import Mathlib.Combinatorics.Matroid.Init

/-!
# Radó's theorem: Riemann surfaces are second countable

Target (lean-eval `rado_riemannSurface`, pure Mathlib): a connected Hausdorff
topological space with a 1-dimensional complex manifold structure has second
countable topology.

This is the exact statement of
<https://lean-lang.org/eval/problems/rado_riemannSurface/>
(submitter: Junyan Xu; source: Hubbard, *Teichmüller theory*, Vol. 1, §1.3).

The real-manifold analogue is false (Prüfer surface, long line), so the proof
must use the complex structure in an essential way.
-/

@[expose] public section

theorem rado_riemannSurface {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] :
    SecondCountableTopology X :=
  Rado.secondCountableTopology_of_riemannSurface
