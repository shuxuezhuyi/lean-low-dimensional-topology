module
public import LowDimensionalTopology.Geometry.Fuchsian.GeometricFiniteness.FiniteSidedGeneration
public import Mathlib.Topology.Connected.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.ParabolicPolygonVertices
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HalfPlanes
@[expose] public section
noncomputable section
open Set Topology
open scoped Pointwise UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
local instance fgCoreSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex := borel Mobius.ExtendedComplex
local instance fgCoreSphereBorel : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- Genuine overlapping connected translates of a connected set form a connected orbit
union when the overlap elements generate the actual whole group. -/
theorem connected_orbit_union_of_generators {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X] (C : Set X) (hC : IsConnected C)
    (T : Set G) (hT : Subgroup.closure T = ⊤)
    (hover : ∀ g ∈ T, (C ∩ g • C).Nonempty) : IsConnected (⋃ g : G, g • C) := by
  classical
  let U : Set X := ⋃ g : G, g • C
  obtain ⟨x,hx⟩ := hC.nonempty
  have hsub (g : G) : g • C ⊆ U := subset_iUnion (fun a : G => a • C) g
  have hcopy (g : G) : IsConnected (g • C) :=
    hC.image (fun y => g • y) (continuous_const_smul g).continuousOn
  have hxU : x ∈ U := hsub 1 (by simpa only [one_smul] using hx)
  have hbase : C ⊆ connectedComponentIn U x := hC.isPreconnected.subset_connectedComponentIn hx
    (by simpa only [one_smul] using hsub 1)
  have hstep (g a : G) (ha : (C ∩ a • C).Nonempty)
      (hg : g • C ⊆ connectedComponentIn U x) : (g*a) • C ⊆ connectedComponentIn U x := by
    obtain ⟨y,hyC,z,hzC,hazy⟩ := ha
    change a • z = y at hazy
    have hgy : g • y ∈ connectedComponentIn U x := hg ⟨y,hyC,rfl⟩
    have hgyz : g • y ∈ (g*a) • C := by
      refine ⟨z,hzC,?_⟩
      change (g*a) • z = g • y
      rw [mul_smul,hazy]
    have hh := (hcopy (g*a)).isPreconnected.subset_connectedComponentIn hgyz (hsub (g*a))
    rw [←connectedComponentIn_eq hgy] at hh
    exact hh
  have hinv (a : G) (ha : (C ∩ a • C).Nonempty) : (C ∩ a⁻¹ • C).Nonempty := by
    obtain ⟨y,hy,z,hz,hazy⟩ := ha
    change a • z = y at hazy
    exact ⟨z,hz,y,hy,by change a⁻¹ • y = z; rw [←hazy]; exact inv_smul_smul a z⟩
  have hall (g : G) (hg : g ∈ Subgroup.closure T) : g • C ⊆ connectedComponentIn U x := by
    induction hg using Subgroup.closure_induction_right with
    | one => simpa only [one_smul] using hbase
    | @mul_right g _ a ha ih => exact hstep g a (hover a ha) ih
    | @mul_inv_cancel g _ a ha ih =>
      simpa only [mul_smul] using hstep g a⁻¹ (hinv a (hover a ha)) ih
  have he : connectedComponentIn U x = U := by
    apply subset_antisymm (connectedComponentIn_subset U x)
    intro y hy
    change y ∈ ⋃ g : G, g • C at hy
    obtain ⟨g,hy⟩ := mem_iUnion.mp hy
    exact hall g (hT ▸ Subgroup.mem_top g) hy
  change IsConnected U
  rw [←he]
  exact isConnected_connectedComponentIn_iff.mpr hxU


/-- Finite generation produces a genuine compact connected polygon core whose actual
whole-group translates form a connected set and which meets its translates by a finite
genuine side-pairing generating family. No finite-end or finite-side conclusion is assumed. -/
theorem IsConvexFuchsianPolygon.finitelyGenerated_compact_connected_core
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hFG : H.FG) :
    ∃ K : Set P.domain.carrier, IsCompact K ∧ IsConnected K ∧ K ⊆ closure D ∧
      (K ∩ D).Nonempty ∧ IsConnected (⋃ g : H, g • K) ∧
      ∃ T : Set H, T.Finite ∧ T ⊆ fuchsianSidePairingElements P D ∧
        Subgroup.closure T = ⊤ ∧ ∀ g ∈ T, (K ∩ g • K).Nonempty := by
  classical
  let : ContinuousConstSMul H P.domain.carrier := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainContinuousConstSMul P.domain
  obtain ⟨T,hTf,hTS,hTgen⟩ := finitelyGenerated_finite_sidePairing_generators hD hFG
  let : Fintype T := hTf.fintype
  have hpair (g : T) : ∃ x ∈ closure D, ∃ y ∈ closure D, g.val • y = x := by
    have hside := (hTS g.property).2
    obtain ⟨x,hx,_y,_hy,_hxy⟩ := hside.2.2
    obtain ⟨y,hy,hgy⟩ := hx.2
    exact ⟨x,hx.1,y,hy,hgy⟩
  choose x hx y hy hgy using hpair
  obtain ⟨w,hw⟩ := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  let φ := P.halfPlaneCoordinate
  let M (g : T) : ℝ := max (dist (φ (x g)) (φ w)) (dist (φ (y g)) (φ w))
  obtain ⟨B,hB⟩ := (Set.finite_range M).bddAbove
  let R := max 1 (B+1)
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let A : Set ℍ := (φ '' closure D) ∩ Metric.closedBall (φ w) R
  let K : Set P.domain.carrier := φ.symm '' A
  have hAc : IsCompact A := (isCompact_closedBall (φ w) R).inter_left
    (φ.isClosedMap _ isClosed_closure)
  have hKc : IsCompact K := hAc.image φ.symm.continuous
  have hKD : K ⊆ closure D := by
    rintro _ ⟨z,⟨⟨u,hu,huφ⟩,_hz⟩,rfl⟩
    rw [←huφ,φ.symm_apply_apply]
    exact hu
  have hmem (u : P.domain.carrier) (hu : u ∈ closure D) (hball : dist (φ u) (φ w) ≤ R) : u ∈ K :=
    ⟨φ u,⟨⟨u,hu,rfl⟩,hball⟩,φ.symm_apply_apply u⟩
  have hwK : w ∈ K := hmem w (subset_closure hw) (by simpa only [dist_self] using hR.le)
  have hcD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (φ '' D) := by
    have hh := hD.normalized_hConvex (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    rw [map_one] at hh
    simpa using hh
  have hcCl : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (φ '' closure D) := by
    rw [φ.image_closure]
    exact hcD.closure
  have hcA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex A := by
    intro z hz u hu v hv
    exact ⟨hcCl z hz.1 u hu.1 hv,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_metric_closedBall (φ w) R) z hz.2 u hu.2 hv⟩
  have hKconn : IsConnected K := ⟨⟨w,hwK⟩,hcA.isPreconnected.image φ.symm φ.symm.continuous.continuousOn⟩
  have hover (g : H) (hg : g ∈ T) : (K ∩ g • K).Nonempty := by
    let G : T := ⟨g,hg⟩
    have hMR : M G ≤ R := (hB (mem_range_self G)).trans (by dsimp [R]; linarith [le_max_right (1:ℝ) (B+1)])
    have hxR : dist (φ (x G)) (φ w) ≤ R := (le_max_left _ _).trans hMR
    have hyR : dist (φ (y G)) (φ w) ≤ R := (le_max_right _ _).trans hMR
    exact ⟨x G,hmem _ (hx G) hxR,y G,hmem _ (hy G) hyR,hgy G⟩
  exact ⟨K,hKc,hKconn,hKD,⟨w,hwK,hw⟩,
    connected_orbit_union_of_generators K hKconn T hTgen hover,T,hTf,hTS,hTgen,hover⟩

end LowDimensionalTopology.Geometry.Fuchsian
