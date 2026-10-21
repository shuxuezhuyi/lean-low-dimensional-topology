module
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeHalfPlaneAnglePairs
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincarePairedSideStars
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)

/-- Literal original boundary copies evaluated at the specified physical point. -/
def BoundaryCopy (z : ℍ) := {a : S.Copy | S.copyEvaluation a=z ∧ a.2.val∈P.boundary}

theorem BoundaryCopy.not_vertex {V : Set ℍ} {z : ℍ} (a : S.BoundaryCopy z)
    (hAvoid : ∀g : S.Generated,z∉g • V) : a.val.2.val∉V := by
  intro hv
  apply hAvoid a.val.1
  exact ⟨a.val.2.val,hv,a.property.1⟩

/-- The original incident side of a literal boundary copy; uniqueness is proved below
when the physical point avoids the actual translated vertex set. -/
def boundaryCopySide {z : ℍ} (a : S.BoundaryCopy z) : P.Side :=
  ⟨(mem_sUnion.mp a.property.2).choose,(mem_sUnion.mp a.property.2).choose_spec.1⟩

theorem boundaryCopySide_mem {z : ℍ} (a : S.BoundaryCopy z) :
    a.val.2.val∈(S.boundaryCopySide a).val :=
  (mem_sUnion.mp a.property.2).choose_spec.2

theorem boundaryCopySide_unique {V : Set ℍ} (D :
  _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    {z : ℍ} (hAvoid : ∀g : S.Generated,z∉g • V) (a : S.BoundaryCopy z)
    (s : P.Side) (hs : a.val.2.val∈s.val) : s=S.boundaryCopySide a := by
  by_contra hne
  exact _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.BoundaryCopy.not_vertex S a hAvoid (D.side_meet_vertex s (S.boundaryCopySide a) hne a.val.2.val hs
    (S.boundaryCopySide_mem a))

/-- The actual paired neighboring boundary copy, with its original group label. -/
def boundaryCopyMate {z : ℍ} (a : S.BoundaryCopy z) : S.BoundaryCopy z :=
  ⟨S.sideMateCopy a.val (S.boundaryCopySide a) (S.boundaryCopySide_mem a),by
    constructor
    · exact (S.step_evaluation (S.step_sideMateCopy a.val (S.boundaryCopySide a)
        (S.boundaryCopySide_mem a))).symm.trans a.property.1
    · exact P.side_subset_boundary (S.paired (S.boundaryCopySide a))
        (S.sideMateCopy_mem_paired a.val (S.boundaryCopySide a) (S.boundaryCopySide_mem a))⟩

theorem boundaryCopyMate_side {V : Set ℍ} (D :
  _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    {z : ℍ} (hAvoid : ∀g : S.Generated,z∉g • V) (a : S.BoundaryCopy z) :
    S.boundaryCopySide (S.boundaryCopyMate a)=S.paired (S.boundaryCopySide a) := by
  apply (S.boundaryCopySide_unique D hAvoid (S.boundaryCopyMate a) _ _).symm
  exact S.sideMateCopy_mem_paired a.val (S.boundaryCopySide a) (S.boundaryCopySide_mem a)

/-- All actual boundary translate labels pair involutively, including self-paired
original sides, without assuming a full tiling or any angular conclusion. -/
theorem boundaryCopyMate_involutive {V : Set ℍ} (D :
  _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    {z : ℍ} (hAvoid : ∀g : S.Generated,z∉g • V) :
    Function.Involutive (S.boundaryCopyMate (z:=z)) := by
  intro a
  apply Subtype.ext
  change S.sideMateCopy (S.sideMateCopy a.val (S.boundaryCopySide a) (S.boundaryCopySide_mem a))
    (S.boundaryCopySide (S.boundaryCopyMate a))
    (S.boundaryCopySide_mem (S.boundaryCopyMate a))=a.val
  have hc (t : P.Side)
      (ht : (S.sideMateCopy a.val (S.boundaryCopySide a) (S.boundaryCopySide_mem a)).2.val∈t.val)
      (he : t=S.paired (S.boundaryCopySide a)) :
      S.sideMateCopy (S.sideMateCopy a.val (S.boundaryCopySide a) (S.boundaryCopySide_mem a)) t ht=a.val := by
    subst t
    exact S.sideMateCopy_paired a.val (S.boundaryCopySide a) (S.boundaryCopySide_mem a)
  exact hc _ _ (S.boundaryCopyMate_side D hAvoid a)

/-- Discreteness and compactness prove actual finiteness of the original boundary-copy
set, preserving all stabilizer and translate labels. -/
theorem boundaryCopies_finite [DiscreteTopology S.Generated] (hP : IsCompact P.carrier) (z : ℍ) :
    {a : S.Copy | S.copyEvaluation a=z ∧ a.2.val∈P.boundary}.Finite := by
  let A : Set S.Copy:={a | S.copyEvaluation a=z ∧ a.2.val∈P.boundary}
  have hf : {g : S.Generated | z∈g • P.carrier}.Finite:=
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite S.Generated
      hP).point_finite z
  have him : (Prod.fst '' A).Finite:=hf.subset (by
    rintro g ⟨a,ha,rfl⟩
    exact ⟨a.2.val,a.2.property,ha.1⟩)
  apply Set.Finite.of_finite_image him
  intro a ha b hb he
  exact S.copy_eq_of_evaluation_same_index he (ha.1.trans hb.1.symm)

/-- The two literal actual boundary-copy labels give a genuine full-angle sum
on a physical neighborhood of their common evaluated point. -/
theorem boundaryCopyMate_local_angle_sum {V : Set ℍ} (D :
  _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (hV : ∀x∈V,∀s : P.Side,x∈s.val →S.element s x∈V)
    {z : ℍ} (hAvoid : ∀g : S.Generated,z∉g • V)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉V →S.OppositeSideNeighborhoods s x)
    (a : S.BoundaryCopy z) :
    ∀ᶠy in 𝓝 z,_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngle P.carrier (a.val.1⁻¹ • y)+
      _root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngle P.carrier ((S.boundaryCopyMate a).val.1⁻¹ • y)=2*Real.pi := by
  have hnot := _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.BoundaryCopy.not_vertex S a hAvoid
  have hpair:=D.paired_side_local_angle_sum S hV a.val.2 (S.boundaryCopySide a)
    (S.boundaryCopySide_mem a) hnot
    (hOpp _ _ (S.boundaryCopySide_mem a) hnot)
  have hinv : a.val.1⁻¹ • z=a.val.2.val := by
    calc
      a.val.1⁻¹ • z=a.val.1⁻¹ • (a.val.1 • a.val.2.val) :=
        congrArg (fun w : ℍ=>a.val.1⁻¹ • w) a.property.1.symm
      _=a.val.2.val := inv_smul_smul _ _
  have ht : Tendsto (fun y : ℍ=>a.val.1⁻¹ • y) (𝓝 z) (𝓝 a.val.2.val) := by
    rw [←hinv]
    exact a.val.1.val.symm.continuous.continuousAt
  filter_upwards [ht.eventually hpair] with y hy
  change _root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngle P.carrier (a.val.1⁻¹ • y)+
    _root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngle P.carrier ((a.val.1*(S.generator (S.boundaryCopySide
      a))⁻¹)⁻¹ • y)=_
  have hgen (w : ℍ) : S.generator (S.boundaryCopySide a) • w=S.element (S.boundaryCopySide a) w := rfl
  simpa only [mul_inv_rev,inv_inv,mul_smul,hgen] using hy

/-- Boundary copies are in genuine bijection with the original group labels whose
actual polygon boundaries contain the physical point. Stabilizers remain counted. -/
def boundaryCopyGroupEquiv (z : ℍ) :
    S.BoundaryCopy z ≃ {g : S.Generated // z∈g • P.boundary} where
  toFun a:=⟨a.val.1,⟨a.val.2.val,a.property.2,a.property.1⟩⟩
  invFun g:=by
    have hb : g.val⁻¹ • z∈P.boundary:=mem_smul_set_iff_inv_smul_mem.mp g.property
    refine ⟨(g.val,⟨g.val⁻¹ • z,Or.inr hb⟩),?_,hb⟩
    exact smul_inv_smul _ _
  left_inv a:=by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change a.val.1⁻¹ • z=a.val.2.val
      calc
        a.val.1⁻¹ • z=a.val.1⁻¹ • (a.val.1 • a.val.2.val) :=
          congrArg (fun w : ℍ=>a.val.1⁻¹ • w) a.property.1.symm
        _=a.val.2.val := inv_smul_smul _ _
  right_inv _:=Subtype.ext rfl

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
