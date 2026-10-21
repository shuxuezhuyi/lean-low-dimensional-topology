module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletGeometry
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual metric half-planes of any original Dirichlet construction contain
each ambient compact set except at finitely many genuine group labels. -/
theorem dirichletHalfPlanes_compact_cofinite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier)
    (K : Set P.domain.carrier) (hK : IsCompact K) :
    {g : H | ¬K⊆dirichletHalfPlane P w g}.Finite := by
  obtain ⟨r,hr⟩:=P.compact_hyperbolicDist_bound w K hK
  apply (P.bounded_orbit_labels w w (2*r)).subset
  intro g hg
  change P.hyperbolicDist (g • w) w≤2*r
  by_contra hfar
  apply hg
  intro z hz
  change P.hyperbolicDist z w<P.hyperbolicDist z (g • w)
  have ht:=P.hyperbolicDist_triangle (g • w) z w
  rw [P.hyperbolicDist_comm (g • w) z] at ht
  have hb:=hr z hz
  linarith only [not_le.mp hfar,ht,hb]

end LowDimensionalTopology.Geometry.Fuchsian
