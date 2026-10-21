/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.CuspRestrictedTopology
/-!
# Original points inside a cusp completion

An admissible sphere point projects to the original quotient exactly when it
belongs to the original invariant disc.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Literal projection of an admissible sphere point lies in the old quotient exactly when that point lies in the unchanged original disc. -/
theorem originalCuspSubsetProjection_mem_old_iff {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D₀:FuchsianDisc H) (K:Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hK:∀z∈K,z∈D₀.carrier∨∃(c:FuchsianCyclicConjugacyClasses D₀ .parabolic)(g:H),
      g.val.val (fuchsianParabolicPointRepresentative D₀ c).val=z) (z:K) :
    fuchsianCuspSubsetProjection D₀ K hK z∈range (fuchsianCuspCompletionOld D₀)↔z.val∈D₀.carrier := by
  constructor
  · rintro ⟨x,hx⟩
    induction x using Quotient.inductionOn with
    | h x=>
        obtain ⟨g,hg⟩:=Quotient.exact hx
        have he:g.val.val z.val=x.val:=congrArg Subtype.val hg
        have hh:=D₀.invariant g⁻¹ x.val x.property
        change g.val.val.symm x.val∈D₀.carrier at hh
        rwa [←he,g.val.val.symm_apply_apply] at hh
  · intro hz
    exact ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D₀.domain ⟨z.val,hz⟩,rfl⟩

end LowDimensionalTopology.Geometry.Fuchsian
