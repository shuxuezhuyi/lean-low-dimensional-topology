module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.EquivariantPath
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletArcDevelopment
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Data.Set.UnionLift
@[expose] public section
noncomputable section
open Set Filter Topology
open scoped Pointwise unitInterval
namespace LowDimensionalTopology.Geometry.Fuchsian













open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Genuine finite generation supplies actual continuous real-parameter curves on
the literal full-orbit neighborhood frontier, equivariant under an actual original
group element and containing a genuine injective initial component arc. This does
not yet assert that the entire real curve is injective or a Jordan curve. -/
theorem finitelyGenerated_actual_equivariant_frontier_curves
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (hFG :
      H.FG)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) (g : H) (hg : g ≠ 1) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ 0 < R ∧
      IsOpen (fuchsianOrbitBallUnion P w R) ∧ IsConnected (fuchsianOrbitBallUnion P w R) ∧
      (dirichletCircleCuts P w R).Finite ∧
      ∀ x : dirichletCircleCuts P w R, ∃ k : H, ∃ F : ℝ → P.domain.carrier,
        Continuous F ∧ F 0 = x.val ∧ (∀ t : ℝ, F (t+1) = k • F t) ∧
        range F ⊆ frontier (fuchsianOrbitBallUnion P w R) ∧
        ∃ q : P.domain.carrier, q ≠ x.val ∧ ∃ δ : Path x.val q,
          Function.Injective δ ∧ range δ ⊆ range F ∧
          range δ \ {x.val,q} ⊆ dirichletDomain P w := by
  let : ContinuousConstSMul H P.domain.carrier := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainContinuousConstSMul P.domain
  obtain ⟨R,hR₀,hR,hOpen,hConn,hFin,hPaths⟩ :=
    finitelyGenerated_developed_frontier_paths P hFG w hw g hg R₀
  refine ⟨R,hR₀,hR,hOpen,hConn,hFin,?_⟩
  intro x
  obtain ⟨k,Γ,hΓ,q,hq,δ,hδi,hδΓ,hδD⟩ := hPaths x
  let F := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k Γ
  have hzero : F 0 = x.val := by
    simpa only [Int.cast_zero,zpow_zero,one_smul] using _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_int k Γ 0
  have hFS : range F ⊆ frontier (fuchsianOrbitBallUnion P w R) := by
    apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_range_subset k Γ _ _ hΓ
    intro n v hv
    have hh : k^n • v ∈ k^n • frontier (fuchsianOrbitBallUnion P w R) := smul_mem_smul_set hv
    rwa [fuchsianOrbitBallUnion_frontier_invariant] at hh
  have hΓF : range Γ ⊆ range F := by
    rintro y ⟨t,rfl⟩
    exact ⟨t,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_unitInterval k Γ t⟩
  exact ⟨k,F,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.continuous_equivariantPathExtension k Γ,hzero,
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_add_one k Γ,hFS,q,hq,δ,hδi,hδΓ.trans hΓF,hδD⟩

end LowDimensionalTopology.Geometry.Fuchsian
