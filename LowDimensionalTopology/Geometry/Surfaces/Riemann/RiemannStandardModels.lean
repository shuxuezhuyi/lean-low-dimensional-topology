module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannManifoldEquivalences
public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.EuclideanQuotientSurfaces
public import LowDimensionalTopology.Geometry.Surfaces.Covering.DiscUniversalDeck
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
@[expose] public section
noncomputable section
open Set Topology Metric
open scoped Manifold ContDiff OnePoint
namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The ordinary open unit disc with its actual Mathlib open-submanifold structure. -/
def standardUnitDiscOpens : TopologicalSpace.Opens ℂ := ⟨ball 0 1, isOpen_ball⟩

instance standardUnitDisc_connectedSpace : ConnectedSpace standardUnitDiscOpens :=
  isConnected_iff_connectedSpace.mp (isConnected_ball (E := ℂ) zero_lt_one)

/-- The original surface language applied to the canonical Mathlib open unit disc manifold. -/
def standardUnitDiscRiemannSurface : RiemannSurface standardUnitDiscOpens :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface.ofManifold standardUnitDiscOpens

/-- The genuine finite chart identifies the inherited sphere subdomain with the native
open unit disc, without transporting or replacing its manifold structure. -/
def standardUnitDiscHomeomorph : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ≃ₜ standardUnitDiscOpens := discFiniteHomeomorph

theorem standardUnitDiscHomeomorph_coe (z : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    (standardUnitDiscHomeomorph z).val = discFiniteChart z := rfl

/-- The finite chart is analytic from the actual inherited sphere atlas into the native
Mathlib open-submanifold atlas. -/
theorem standardUnitDiscHomeomorph_analytic :
    RiemannAnalyticMap discRiemannSurface.toRiemannAtlas
      standardUnitDiscRiemannSurface.toRiemannAtlas standardUnitDiscHomeomorph := by
  apply (riemannAnalyticMap_iff_locally _ _ _).mpr
  refine ⟨standardUnitDiscHomeomorph.continuous, ?_⟩
  intro x
  refine ⟨discFiniteChart, discFiniteChart_mem, discFiniteChart_source.symm ▸ Set.mem_univ x,
    chartAt ℂ (standardUnitDiscHomeomorph x), chart_mem_atlas ℂ _, mem_chart_source ℂ _, ?_⟩
  apply analyticAt_id.congr
  filter_upwards [discFiniteChart.open_target.mem_nhds
    (discFiniteChart.map_source (discFiniteChart_source.symm ▸ Set.mem_univ x))] with z hz
  change z = discFiniteChart (discFiniteChart.symm z)
  exact (discFiniteChart.right_inv hz).symm

/--
The geometric inherited extended disc and the genuine standard analytic open disc are
conformally equivalent in their original complex structures.
-/
theorem discRiemannSurface_conformallyEquivalent_standardUnitDisc :
    RiemannConformallyEquivalent discRiemannSurface standardUnitDiscRiemannSurface :=
  ⟨standardUnitDiscHomeomorph, standardUnitDiscHomeomorph_analytic, standardUnitDiscHomeomorph.bijective⟩

/-- The standard complex-plane manifold already has precisely the geometric global-chart structure. -/
theorem complexPlaneRiemannSurface_conformallyEquivalent_manifold :
    RiemannConformallyEquivalent complexPlaneRiemannSurface (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface.ofManifold ℂ) :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannConformallyEquivalent.refl complexPlaneRiemannSurface


/-- Reading the original atlas as a manifold and reading its atlas back recovers the same
atlas. Only its chart set enters this assertion; chartAt choices need not be equal. -/
theorem RiemannAtlas.ofManifold_toChartedSpace {X : Type*} [TopologicalSpace X] (A : RiemannAtlas X) :
    let := A.toChartedSpace
    let := A.isManifold
    _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas.ofManifold X = A := by
  rfl

/-- The surface structure is recovered exactly after passage through its analytic manifold. -/
theorem RiemannSurface.ofManifold_toChartedSpace {X : Type*} [TopologicalSpace X] (R : RiemannSurface X) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R.t2Space
    let := R.connectedSpace
    _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface.ofManifold X = R := by
  rfl

/-- A surface conformally equivalent to the canonical Mathlib open disc is of the
literal source hyperbolic type, by its genuine analytic disc covering. -/
theorem riemannSurface_isHyperbolicType_of_conformallyEquivalent_standardUnitDisc
    {X : Type*} [TopologicalSpace X] (R : RiemannSurface X)
    (hR : RiemannConformallyEquivalent R standardUnitDiscRiemannSurface) : IsHyperbolicType R := by
  obtain ⟨f, hf, hbij⟩ := hR.trans discRiemannSurface_conformallyEquivalent_standardUnitDisc.symm
  let E := hf.toHomeomorph hbij
  have hp : IsCoveringMap E.symm := by
    apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
    exact E.symm.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
      (fun x _hx => (Set.finite_singleton x).preimage E.symm.injective.injOn)
      E.symm.isLocalHomeomorph.isLocalHomeomorphOn
  exact riemannSurface_isHyperbolicType_of_discCover R E.symm hp (hf.inverse_analytic hbij) E.symm.surjective

/-- The canonical open-disc alternative for a genuinely constructed universal cover
implies hyperbolic type of the original base surface. -/
theorem RiemannUniversalCover.isHyperbolicType_of_conformallyEquivalent_standardUnitDisc
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X} (C : RiemannUniversalCover R)
    (hC : @RiemannConformallyEquivalent C.space standardUnitDiscOpens C.topology _
      C.surface standardUnitDiscRiemannSurface) : IsHyperbolicType R := by
  let : TopologicalSpace C.space := C.topology
  exact C.isHyperbolicType_of_conformallyEquivalent_disc
    (hC.trans discRiemannSurface_conformallyEquivalent_standardUnitDisc.symm)

end LowDimensionalTopology.Geometry.Surfaces
