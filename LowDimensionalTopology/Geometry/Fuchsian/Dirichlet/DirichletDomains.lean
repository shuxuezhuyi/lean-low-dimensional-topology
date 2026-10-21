/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonCycles
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSides
public import LowDimensionalTopology.Geometry.DiscreteGroups.Discreteness.DiscretenessCriteria
@[expose] public section
open Set Filter
open scoped Topology OnePoint UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- The actual original Fuchsian point in the genuine half-plane coordinate. -/
def UnitDiscFuchsianGroup.halfPlaneCoordinate {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : P.domain.carrier ≃ₜ ℍ:=P.finiteCoordinate.trans _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm

/-- The genuine hyperbolic path metric, expressed on the original actual disc points. -/
def UnitDiscFuchsianGroup.hyperbolicDist {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x y : P.domain.carrier) : ℝ:=
  dist (P.halfPlaneCoordinate x) (P.halfPlaneCoordinate y)

theorem UnitDiscFuchsianGroup.hyperbolicDist_eq_discPathDist {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x y : P.domain.carrier) :
    P.hyperbolicDist x y=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (P.finiteCoordinate
      x) (P.finiteCoordinate y) :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane _ _).symm

theorem UnitDiscFuchsianGroup.hyperbolicDist_comm {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x y : P.domain.carrier) : P.hyperbolicDist x y=P.hyperbolicDist y x:=dist_comm _ _

theorem UnitDiscFuchsianGroup.hyperbolicDist_nonneg {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x y : P.domain.carrier) : 0≤P.hyperbolicDist x y:=dist_nonneg

theorem UnitDiscFuchsianGroup.hyperbolicDist_self {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) : P.hyperbolicDist x x=0:=dist_self _

theorem UnitDiscFuchsianGroup.hyperbolicDist_pos {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) {x y : P.domain.carrier} : 0<P.hyperbolicDist x y ↔ x≠y:=by
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.hyperbolicDist,dist_pos]
  exact P.halfPlaneCoordinate.injective.ne_iff

theorem UnitDiscFuchsianGroup.hyperbolicDist_triangle {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x y z : P.domain.carrier) :
    P.hyperbolicDist x z≤P.hyperbolicDist x y+P.hyperbolicDist y z:=dist_triangle _ _ _

theorem UnitDiscFuchsianGroup.hyperbolicDist_continuous {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : Continuous (fun p : P.domain.carrier×P.domain.carrier=>P.hyperbolicDist p.1 p.2):=
  (P.halfPlaneCoordinate.continuous.comp continuous_fst).dist (P.halfPlaneCoordinate.continuous.comp continuous_snd)

theorem UnitDiscFuchsianGroup.hyperbolicDist_smul {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (x y : P.domain.carrier) :
    P.hyperbolicDist (g • x) (g • y)=P.hyperbolicDist x y := by
  let :=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  rw [P.hyperbolicDist_eq_discPathDist,P.hyperbolicDist_eq_discPathDist]
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance]
  have he (u : P.domain.carrier) : P.discAction g (P.finiteCoordinate u)=P.finiteCoordinate (g • u):=by
    change P.finiteCoordinate ((Homeomorph.smul g) (P.finiteCoordinate.symm (P.finiteCoordinate u)))=_
    rw [P.finiteCoordinate.symm_apply_apply]
    rfl
  simpa only [he] using (P.discAction_isometry g).dist_eq (P.finiteCoordinate x) (P.finiteCoordinate y)

theorem UnitDiscFuchsianGroup.hyperbolicDist_inverse_smul {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (x y : P.domain.carrier) :
    P.hyperbolicDist x (g • y)=P.hyperbolicDist (g⁻¹ • x) y := by
  rw [←P.hyperbolicDist_smul g (g⁻¹ • x) y,smul_inv_smul]

/-- The source center condition is stated for the actual original group action. -/
def IsDirichletCenter {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) : Prop:=∀g : H,g • w=w → g=1

/-- The genuine bisector of the center and its original orbit image. -/
def dirichletBisector {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (g : H) : Set P.domain.carrier:=
  {z | P.hyperbolicDist z w=P.hyperbolicDist z (g • w)}

/-- The source's center-containing strict metric half-plane. -/
def dirichletHalfPlane {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (g : H) : Set P.domain.carrier:=
  {z | P.hyperbolicDist z w<P.hyperbolicDist z (g • w)}

/-- For the original actual Fuchsian action and genuine path metric. -/
def dirichletDomain {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) : Set P.domain.carrier:=
  {z | ∀g : H,g≠1 → z∈dirichletHalfPlane P w g}

theorem dirichletHalfPlane_isOpen {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (g : H) : IsOpen (dirichletHalfPlane P w g):=by
  change IsOpen {z | dist (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate w)<
    dist (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate (g • w))}
  exact isOpen_lt (P.halfPlaneCoordinate.continuous.dist continuous_const)
    (P.halfPlaneCoordinate.continuous.dist continuous_const)

theorem dirichletBisector_isClosed {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (g : H) : IsClosed (dirichletBisector P w g):=by
  change IsClosed {z | dist (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate w)=
    dist (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate (g • w))}
  exact isClosed_eq (P.halfPlaneCoordinate.continuous.dist continuous_const)
    (P.halfPlaneCoordinate.continuous.dist continuous_const)

theorem dirichletHalfPlane_mem_inverse {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w z : P.domain.carrier) (g : H) : z∈dirichletHalfPlane P w g ↔ w∈dirichletHalfPlane P z g⁻¹ := by
  change P.hyperbolicDist z w<P.hyperbolicDist z (g • w) ↔
    P.hyperbolicDist w z<P.hyperbolicDist w (g⁻¹ • z)
  rw [P.hyperbolicDist_inverse_smul g,P.hyperbolicDist_comm z w,
    P.hyperbolicDist_comm (g⁻¹ • z) w]

theorem dirichletDomain_mem_symmetry {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P
  : UnitDiscFuchsianGroup H)
    (w z : P.domain.carrier) : z∈dirichletDomain P w ↔ w∈dirichletDomain P z := by
  constructor
  · intro hz g hg
    exact (dirichletHalfPlane_mem_inverse P z w g).mpr (hz g⁻¹ (inv_ne_one.mpr hg))
  · intro hw g hg
    exact (dirichletHalfPlane_mem_inverse P w z g).mpr (hw g⁻¹ (inv_ne_one.mpr hg))

theorem dirichletDomain_center_mem {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) : w∈dirichletDomain P w := by
  intro g hg
  change P.hyperbolicDist w w<P.hyperbolicDist w (g • w)
  rw [P.hyperbolicDist_self]
  apply P.hyperbolicDist_pos.mpr
  exact fun he=>hg (hw g he.symm)

theorem dirichletDomain_nonempty {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) : (dirichletDomain P w).Nonempty:=
  ⟨w,dirichletDomain_center_mem P w hw⟩

theorem closure_dirichletDomain_le {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) {z : P.domain.carrier} (hz : z∈closure (dirichletDomain P w)) (g : H) :
    P.hyperbolicDist z w≤P.hyperbolicDist z (g • w) := by
  by_cases hg : g=1
  · subst g
    simp only [one_smul,le_refl]
  · have hc : IsClosed {z | P.hyperbolicDist z w≤P.hyperbolicDist z (g • w)}:=by
      change IsClosed {z | dist (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate w)≤
        dist (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate (g • w))}
      exact isClosed_le (P.halfPlaneCoordinate.continuous.dist continuous_const)
        (P.halfPlaneCoordinate.continuous.dist continuous_const)
    apply closure_minimal ?_ hc hz
    intro x hx
    change P.hyperbolicDist x w≤P.hyperbolicDist x (g • w)
    exact (hx g hg).le

/-- The actual original-orbit closed-domain distance equality, including possible elliptic cycle points. -/
theorem dirichlet_closed_orbit_equal_distance {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w x : P.domain.carrier) (g : H) (hx : x∈closure (dirichletDomain P w))
    (hyg : g • x∈closure (dirichletDomain P w)) : P.hyperbolicDist x w=P.hyperbolicDist (g • x) w := by
  apply le_antisymm
  · have h:=closure_dirichletDomain_le P w hx g⁻¹
    rw [P.hyperbolicDist_inverse_smul g⁻¹,inv_inv] at h
    exact h
  · have h:=closure_dirichletDomain_le P w hyg g
    rw [P.hyperbolicDist_smul g] at h
    exact h


theorem UnitDiscFuchsianGroup.fixed_interior_elliptic {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (g : H) (hg : g≠1) (hfix : g • w=w) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val := by
  have hn : g.val≠1:=fun he=>hg (Subtype.ext he)
  have hf : g.val.val w.val=w.val:=congrArg Subtype.val hfix
  have hOff : w.val∉frontier P.domain.carrier:=by
    intro hh
    change w.val∈closure P.domain.carrier ∧ w.val∉interior P.domain.carrier at hh
    exact hh.2 (P.domain.isOpen.interior_eq.symm ▸ w.property)
  rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_type_trichotomy g.val hn with hpa | hlo | hel
  · exact (hOff (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_fixed_mem_disc_frontier g.val hpa
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc (P.image_eq g) hf)).elim
  · exact (hOff (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_fixed_mem_disc_frontier g.val
      ⟨hlo,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc,P.image_eq g⟩
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc (P.image_eq g) hf)).elim
  · exact hel

/-- The actual center condition is exactly the source exclusion of elliptic fixed points. -/
theorem isDirichletCenter_iff_not_ellipticFixed {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) :
    IsDirichletCenter P w ↔ w.val∉_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFixedPointSet H := by
  constructor
  · intro hw ⟨g,hg,hfix⟩
    have he : g=1:=hw g (Subtype.ext hfix)
    exact hg.1 (congrArg Subtype.val he)
  · intro hno g hfix
    by_contra hg
    exact hno ⟨g,P.fixed_interior_elliptic w g hg hfix,congrArg Subtype.val hfix⟩

/-- Every actual closed Dirichlet orbit cycle is equidistant from its true center. -/
theorem dirichlet_cycle_distance_to_center_eq {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w z : P.domain.carrier) {x y : P.domain.carrier}
    (hx : x∈fuchsianPolygonCycle P (dirichletDomain P w) z)
    (hy : y∈fuchsianPolygonCycle P (dirichletDomain P w) z) :
    P.hyperbolicDist x w=P.hyperbolicDist y w := by
  obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp hx.2
  obtain ⟨h,hh⟩:=MulAction.mem_orbit_iff.mp hy.2
  have he : (h*g⁻¹) • x=y:=by rw [←hg,mul_smul,inv_smul_smul,hh]
  have hi : (h*g⁻¹) • x∈closure (dirichletDomain P w):=he.symm ▸ hy.1
  have hd:=dirichlet_closed_orbit_equal_distance P w x (h*g⁻¹) hx.1 hi
  rwa [he] at hd

end
end LowDimensionalTopology.Geometry.Fuchsian
