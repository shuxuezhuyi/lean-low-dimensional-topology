/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.StabilizerDirichletRegions
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ConvexFiniteRotationSectors
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveEllipticAngles
/-!
# Fundamental sectors for finite rotation groups

Primitive finite rotations act on the full unit disc. Their open angular
sectors have unique orbit representatives and closed-sector orbit coverage.
For order at least two, the sectors are convex locally finite fundamental polygons.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology OnePoint Pointwise Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance finiteSectorSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance finiteSectorSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- Literal unit rotations as actual orientation-preserving Mobius transformations. -/
def finiteMobiusRotationHom : Circle →* _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom.comp Circle.toUnits

def finiteMobiusRotationGroup (n : ℕ) : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  Subgroup.zpowers (finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator
    n))

theorem finiteMobiusRotation_mem_fin (n : ℕ) (hn : 0 < n)
    (g : finiteMobiusRotationGroup n) :
    ∃ i : Fin n, g.val = finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^ i.val) := by
  obtain ⟨k,hk⟩ := Subgroup.mem_zpowers_iff.mp g.property
  obtain ⟨i,hi⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_zpow_eq_fin n hn k
  refine ⟨i,?_⟩
  change (finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator
    n)) ^ k = g.val at hk
  rw [←hk,←map_zpow,hi]

theorem finiteMobiusRotation_power_mem (n i : ℕ) :
    finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^ i) ∈ finiteMobiusRotationGroup n := by
  rw [map_pow]
  exact (finiteMobiusRotationGroup n).pow_mem (Subgroup.mem_zpowers _) i

theorem finiteMobiusRotation_finite (n : ℕ) (hn : 0 < n) : Finite (finiteMobiusRotationGroup n) := by
  let f : Fin n → finiteMobiusRotationGroup n := fun i =>
    ⟨finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^
      i.val),finiteMobiusRotation_power_mem n i.val⟩
  apply Finite.of_surjective f
  intro g
  obtain ⟨i,hi⟩ := finiteMobiusRotation_mem_fin n hn g
  exact ⟨i,Subtype.ext hi.symm⟩

/-- This finite actual rotation group is a genuine Fuchsian group on the actual entire unit disc. -/
theorem finiteMobiusRotationData (n : ℕ) (hn : 0 < n) :
    UnitDiscFuchsianGroup (finiteMobiusRotationGroup n) where
  invariant g z hz := by
    obtain ⟨i,hi⟩ := finiteMobiusRotation_mem_fin n hn g
    obtain ⟨w,hw,rfl⟩ := hz
    change g.val.val (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
    rw [hi]
    change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Circle.toUnits _)).val (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedUnitDisc,norm_mul]
    simpa using hw
  discontinuous := by
    let finiteSectorFiniteGroup := finiteMobiusRotation_finite n hn
    intro K hK hKD
    exact Set.toFinite _

/-- The literal actual open angular sector, with original group action and density area. -/
def finiteMobiusRotationDomain (n : ℕ) (hn : 0 < n) : Set (finiteMobiusRotationData n hn).domain.carrier :=
  (finiteMobiusRotationData n
    hn).finiteCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector n

theorem finiteMobiusRotation_finite_action (n : ℕ) (hn : 0 < n)
    (i : ℕ) (x : (finiteMobiusRotationData n hn).domain.carrier) :
    ((finiteMobiusRotationData n hn).finiteCoordinate
      ((⟨finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^
        i),finiteMobiusRotation_power_mem n i⟩ :
        finiteMobiusRotationGroup n) • x) : ℂ) =
        (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^ i : Circle) *
          ((finiteMobiusRotationData n hn).finiteCoordinate x : ℂ) := by
  apply OnePoint.coe_injective
  have hc (y : (finiteMobiusRotationData n hn).domain.carrier) :
      ((((finiteMobiusRotationData n hn).finiteCoordinate y : Complex.UnitDisc) : ℂ) :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = y.val :=
    (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe ((finiteMobiusRotationData n
      hn).finiteCoordinate y)).symm.trans
      (congrArg Subtype.val ((finiteMobiusRotationData n hn).finiteCoordinate.symm_apply_apply y))
  rw [hc]
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Circle.toUnits
    (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^ i))).val x.val = _
  rw [←hc x,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe]
  rfl

theorem finiteMobiusRotationDomain_isOpen (n : ℕ) (hn : 0 < n) :
    IsOpen (finiteMobiusRotationDomain n hn) :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector_isOpen
    n).preimage (finiteMobiusRotationData n hn).finiteCoordinate.continuous

theorem finiteMobiusRotationDomain_convex (n : ℕ) (hn : 2 ≤ n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex ((finiteMobiusRotationData n (by omega)).finiteCoordinate ''
      finiteMobiusRotationDomain n (by omega)) := by
  rw [finiteMobiusRotationDomain,(finiteMobiusRotationData n (by omega)).finiteCoordinate.surjective.image_preimage]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector_hConvex n hn

/-- The native disc closure is the literal closed sector intersected with the native disc. -/
theorem finiteRotationDiscSector_closure (n : ℕ) (hn : 0 < n) :
    closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector n) =
      (fun z : Complex.UnitDisc => (z : ℂ)) ⁻¹' _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector n := by
  have he : Topology.IsOpenEmbedding (fun z : Complex.UnitDisc => (z : ℂ)) := by
    refine ⟨Complex.UnitDisc.isEmbedding_coe,?_⟩
    have hr : range (fun z : Complex.UnitDisc => (z : ℂ)) = Metric.ball 0 1 := by
      ext z
      constructor
      · rintro ⟨w,rfl⟩;simpa only [Metric.mem_ball,dist_zero_right] using w.norm_lt_one
      · intro hz
        exact ⟨Complex.UnitDisc.mk z (by simpa only [Metric.mem_ball,dist_zero_right] using hz),rfl⟩
    rw [hr]
    exact Metric.isOpen_ball
  have hf := he.isOpenMap
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector,←hf.preimage_closure_eq_closure_preimage
    Complex.UnitDisc.continuous_coe,_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector_closure n hn]

theorem finiteMobiusRotationDomain_closure (n : ℕ) (hn : 0 < n) :
    closure (finiteMobiusRotationDomain n hn) =
      (fun x => ((finiteMobiusRotationData n hn).finiteCoordinate x : ℂ)) ⁻¹'
        _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector n := by
  rw [finiteMobiusRotationDomain,←(finiteMobiusRotationData n hn).finiteCoordinate.preimage_closure,
    finiteRotationDiscSector_closure n hn]
  rfl

/-- Every positive finite angular period has genuine interior points in the actual disc. -/
theorem finiteMobiusRotationDomain_nonempty (n : ℕ) (hn : 0 < n) :
    (finiteMobiusRotationDomain n hn).Nonempty := by
  let t := _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n / 2
  have ht : t ∈ Ioo (0:ℝ) (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n) := by
    have hp := _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod_pos n hn
    constructor <;> dsimp [t] <;> linarith
  let z : Complex.UnitDisc := Complex.UnitDisc.mk ((1/2:ℂ) * (Circle.exp t : ℂ)) (by
    rw [norm_mul,Circle.norm_coe]
    norm_num)
  refine ⟨(finiteMobiusRotationData n hn).finiteCoordinate.symm z,?_⟩
  change ((finiteMobiusRotationData n hn).finiteCoordinate
    ((finiteMobiusRotationData n hn).finiteCoordinate.symm
      z) : ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n
  rw [(finiteMobiusRotationData n hn).finiteCoordinate.apply_symm_apply]
  refine (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector_mem_iff n _).mpr ⟨1/2,by norm_num,t,ht,?_⟩
  change (1/2:ℂ) * (Circle.exp t : ℂ) = ((1/2:ℝ):ℂ) * (Circle.exp t : ℂ)
  norm_num

/-- Actual original Mobius rotates the closed sector onto an orbit cover of the entire disc. -/
theorem finiteMobiusRotationDomain_closure_meetsEveryOrbit (n : ℕ) (hn : 0 < n) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit (finiteMobiusRotationGroup
      n) (finiteMobiusRotationData n hn).domain.carrier
      (closure (finiteMobiusRotationDomain n hn)) := by
  intro x
  let P := finiteMobiusRotationData n hn
  have hxball : (P.finiteCoordinate x : ℂ) ∈ Metric.ball 0 1 := by
    simpa only [Metric.mem_ball,dist_zero_right] using (P.finiteCoordinate x).norm_lt_one
  rw [←_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotation_closedPlaneSector_ball_cover n hn 1] at hxball
  obtain ⟨i,w,hw,he⟩ := mem_iUnion.mp hxball
  let z : Complex.UnitDisc := Complex.UnitDisc.mk w (by
    simpa only [Metric.mem_ball,dist_zero_right] using hw.2)
  let y := P.finiteCoordinate.symm z
  let g : finiteMobiusRotationGroup n :=
    ⟨finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^
      i.val),finiteMobiusRotation_power_mem n i.val⟩
  have hgy : g • y = x := by
    apply P.finiteCoordinate.injective
    apply Complex.UnitDisc.coe_injective
    rw [finiteMobiusRotation_finite_action n hn i.val y]
    change (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^ i.val : Circle) *
      (P.finiteCoordinate (P.finiteCoordinate.symm z) : ℂ) = _
    rw [P.finiteCoordinate.apply_symm_apply]
    exact he
  refine ⟨g⁻¹,?_⟩
  have hback : g⁻¹ • x = y := by rw [←hgy,inv_smul_smul]
  rw [hback,finiteMobiusRotationDomain_closure n hn]
  change (P.finiteCoordinate (P.finiteCoordinate.symm z) :
    ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector n
  rw [P.finiteCoordinate.apply_symm_apply]
  exact hw.1

/-- Distinct literal open sectors cannot contain different representatives of one actual orbit. -/
theorem finiteMobiusRotationDomain_orbit_unique (n : ℕ) (hn : 0 < n)
    (x y : (finiteMobiusRotationData n hn).domain.carrier)
    (hx : x ∈ finiteMobiusRotationDomain n hn) (hy : y ∈ finiteMobiusRotationDomain n hn)
    (hxy : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (finiteMobiusRotationGroup n) _
      x =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (finiteMobiusRotationGroup n) _ y) : x = y := by
  let P := finiteMobiusRotationData n hn
  obtain ⟨g,hgy⟩ := (Quotient.exact hxy : MulAction.orbitRel (finiteMobiusRotationGroup n) _ x y)
  change g • y = x at hgy
  obtain ⟨i,hi⟩ := finiteMobiusRotation_mem_fin n hn g
  have hg : g = ⟨finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^
    i.val),
      finiteMobiusRotation_power_mem n i.val⟩ := Subtype.ext hi
  rw [hg] at hgy
  have he := congrArg (fun z => (P.finiteCoordinate z : ℂ)) hgy
  rw [finiteMobiusRotation_finite_action n hn i.val y] at he
  have hx' : (P.finiteCoordinate x :
    ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n := hx
  have hy' : (P.finiteCoordinate y :
    ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n := hy
  by_cases hi0 : i.val = 0
  · apply P.finiteCoordinate.injective
    apply Complex.UnitDisc.coe_injective
    simpa only [hi0,pow_zero,Circle.coe_one,one_mul] using he.symm
  · have hiNe : i ≠ (⟨0,hn⟩ : Fin n) := by intro hh;exact hi0 (congrArg Fin.val hh)
    exact False.elim ((Set.disjoint_left.mp
      (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotation_openPlaneSector_finite_disjoint n hn hiNe))
      ⟨P.finiteCoordinate y,hy',he⟩ ⟨P.finiteCoordinate x,hx',by simp⟩)

/-- A literal primitive finite rotation sector is a genuine full fundamental domain, including its fixed center on the boundary. -/
theorem finiteMobiusRotationDomain_fundamental (n : ℕ) (hn : 2 ≤ n) :
    IsFuchsianFundamentalDomain (finiteMobiusRotationData n (by omega))
      (finiteMobiusRotationDomain n (by omega)) := by
  have hn0 : 0 < n := by omega
  let P := finiteMobiusRotationData n hn0
  have hc := finiteMobiusRotationDomain_convex n hn
  refine ⟨finiteMobiusRotationDomain_isOpen n hn0,
    ⟨finiteMobiusRotationDomain_nonempty n hn0,?_⟩,?_,P.convex_frontier_area_zero hc⟩
  · have he : P.finiteCoordinate.symm '' (P.finiteCoordinate '' finiteMobiusRotationDomain n hn0) =
        finiteMobiusRotationDomain n hn0 := P.finiteCoordinate.symm_image_image _
    rw [←he]
    exact hc.isPreconnected.image _ P.finiteCoordinate.symm.continuous.continuousOn
  · exact exists_fundamentalSet_between _ _ subset_closure
      (finiteMobiusRotationDomain_closure_meetsEveryOrbit n hn0)
      (fun x hx y hy hxy => finiteMobiusRotationDomain_orbit_unique n hn0 x y hx hy hxy)

/-- Finite actual primitive rotations give actual convex locally finite fundamental polygons. -/
theorem finiteMobiusRotationDomain_polygon (n : ℕ) (hn : 2 ≤ n) :
    IsConvexFuchsianPolygon (finiteMobiusRotationData n (by omega))
      (finiteMobiusRotationDomain n (by omega)) := by
  let finiteSectorFiniteGroup := finiteMobiusRotation_finite n (by omega)
  exact ⟨⟨finiteMobiusRotationDomain_fundamental n hn,fun K hK => Set.toFinite _⟩,
    finiteMobiusRotationDomain_convex n hn⟩

end LowDimensionalTopology.Geometry.Fuchsian
