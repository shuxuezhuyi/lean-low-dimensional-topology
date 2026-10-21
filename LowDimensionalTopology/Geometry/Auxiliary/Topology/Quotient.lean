/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Maps.Basic

/-!
# Quotient topology

The quotient topology, its comparison with an existing topology, and continuity of maps from the quotient.
-/

public section

open Topology

universe u v w

namespace LowDimensionalTopology.Geometry.Auxiliary.Topology

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- The topology coinduced by the given map. -/
abbrev quotientTopology [TopologicalSpace X] (f : X → Y) : TopologicalSpace Y :=
  TopologicalSpace.coinduced f inferInstance

/-- The open-set criterion for the coinduced topology. -/
theorem isOpen_quotientTopology_iff [TopologicalSpace X] (f : X → Y) (s : Set Y) :
    @IsOpen Y (quotientTopology f) s ↔ IsOpen (f ⁻¹' s) :=
  Iff.rfl

/-- Continuity implies the quotient-topology inequality without a surjectivity hypothesis. -/
theorem quotientTopology_le_of_continuous [TopologicalSpace X] [tY : TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) : quotientTopology f ≤ tY :=
  hf.coinduced_le


theorem quotientTopology_eq_of_continuous_open_surjective [TopologicalSpace X] [tY : TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) (hopen : IsOpenMap f) (hsurj : Function.Surjective f) :
    quotientTopology f = tY :=
  (hopen.isQuotientMap hf hsurj).eq_coinduced.symm

/-- no surjectivity assumption is needed. -/
theorem continuous_quotientTopology_iff_comp [TopologicalSpace X] [tZ : TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) :
    Continuous[quotientTopology f, tZ] g ↔ Continuous (g ∘ f) :=
  continuous_coinduced_dom

end LowDimensionalTopology.Geometry.Auxiliary.Topology
