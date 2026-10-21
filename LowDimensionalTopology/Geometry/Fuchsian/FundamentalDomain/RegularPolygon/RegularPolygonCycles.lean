/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.RegularPolygon.RegularPolygonPairing
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.AngularMeasure
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaFinite
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.FiniteAreaIdealBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.FiniteRotationFundamentalDomains
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.NativeTriangleProperness
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonAccidentalCycles

/-!
# Vertex cycles of regular fundamental polygons

Opposite-side transformations of the regular polygon determine an explicit full
vertex cycle. Its accumulated transformation is computed through rotations and
reflections; local sectors verify the cycle and opposite-side neighborhood
conditions needed for the native fundamental-domain theorem.

Transport to the original disc action gives one accidental cycle containing all
vertices, equal side lengths, and equality in the stated circumradius formula.
The local hyperbolic disc metric is installed only for the sector calculations.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set InnerProductGeometry
open scoped Complex.UnitDisc Topology UpperHalfPlane ComplexConjugate Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

def regularNativeRotationCircleHom : Circle →* (ℍ ≃ᵢ ℍ) where
  toFun u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap u false)
  map_one':=by rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_one,map_one]
  map_mul' u v:=by
    rw [←map_mul,_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_mul]
    rfl

theorem regularNativeRotation_pow (n : ℕ) (hn : 0<n) :
    regularNativeRotation n ^ n=1 := by
  change regularNativeRotationCircleHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n)^n=1
  rw [←map_pow,(_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_isPrimitiveRoot n
    hn.ne').pow_eq_one,map_one]

theorem regularNativeRotation_pow_vertex (n : ℕ) (hn : 4<n) (j : ℕ) (i : Fin n) :
    (regularNativeRotation n ^ j)
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon n hn)
        (regularCyclePolygon_vertices_finite hn) i)=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon n
        hn) (regularCyclePolygon_vertices_finite hn)
        (((finRotate n)^[j]) i) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ',IsometryEquiv.mul_apply,ih,regularNativeRotation_vertex,
      Function.iterate_succ_apply']

theorem regularNativeRotation_line (n : ℕ) (hn : 4<n) (i : Fin n) :
    regularNativeRotation n '' (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (regularCyclePolygon n
      hn) i).carrier=
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (regularCyclePolygon n hn) (finRotate n i)).carrier := by
  let Q:=regularCyclePolygon n hn
  let hf:=regularCyclePolygon_vertices_finite hn
  let f:=regularNativeRotation n
  obtain ⟨g,hg⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isometry_exists_realGL f.isometry
  rw [hg]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_image_line_of_corresponding_points g _ _
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_injective Q hf).ne (Q.next_ne_self i).symm)
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_left_mem Q hf i))
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_right_mem Q hf i))
  · rw [←congrFun hg (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)]
    change regularNativeRotation n _∈_
    rw [regularNativeRotation_vertex]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q _ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_left_mem Q hf _)
  · rw [←congrFun hg (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (finRotate n i))]
    change regularNativeRotation n _∈_
    rw [regularNativeRotation_vertex]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q _ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_right_mem Q hf _)

theorem regularPlanarRotation_unit_vertex (n : ℕ) (hn : 4<n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) false
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*(i:ℝ)+1)*Real.pi/n))=
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*((finRotate n i):ℝ)+1)*Real.pi/n) := by
  rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_apply]
  simp only [Bool.false_eq_true,ite_false,_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator,_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod,
    Circle.coe_exp]
  have hunit (a : ℝ) : Complex.exp (a*Complex.I)=_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit a:=by
    simp only [_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit,circleMap_zero,Complex.ofReal_one,one_mul]
  rw [hunit]
  exact regularCycleVertex_rotation_angle hn i

theorem regularSideExchangeLinear_rotation (n : ℕ) (hn : 4<n) (i : Fin n) :
    let R:=_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) false
    R*regularSideExchangeLinear n i*R⁻¹=regularSideExchangeLinear n (finRotate n i) := by
  let R:=_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) false
  let U:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*(i:ℝ)+1)*Real.pi/n)
  let V:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*((finRotate n i):ℝ)+1)*Real.pi/n)
  have hU : R U=V:=regularPlanarRotation_unit_vertex n hn i
  have hpoint : (R*regularSideExchangeLinear n i*R⁻¹) V=
      regularSideExchangeLinear n (finRotate n i) V := by
    change R (regularSideExchangeLinear n i (R⁻¹ V))=_
    rw [←hU]
    change R (regularSideExchangeLinear n i (R.symm (R U)))=_
    rw [R.symm_apply_apply,hU]
    rw [regularSideExchangeLinear_phase n hn i,map_neg]
    change -R V=regularSideExchangeLinear n (finRotate n i) V
    rw [regularSideExchangeLinear_phase n hn (finRotate n i),
      regularPlanarRotation_unit_vertex n hn (finRotate n i)]
  have hV : V≠0:=by
    have hv : ‖V‖=1:=by simp [V,_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit]
    intro hv0
    rw [hv0,norm_zero] at hv
    norm_num at hv
  dsimp only [R,regularSideExchangeLinear] at hpoint ⊢
  rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_inv,_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_mul,
    _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_mul] at hpoint ⊢
  simp only [Bool.false_eq_true,ite_false,Bool.false_xor,Bool.true_xor,
    ite_true,inv_inv,Bool.not_false] at hpoint ⊢
  have hc := hpoint
  simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_apply,ite_true] at hc
  have hcoef := mul_right_cancel₀ (show conj V≠0 by simpa using hV) hc
  apply LinearIsometryEquiv.ext
  intro z
  simp [_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_apply,hcoef]

theorem regularNativeSideExchange_rotation (n : ℕ) (hn : 4<n) (i : Fin n) :
    regularNativeRotation n*regularNativeSideExchange n i*(regularNativeRotation n)⁻¹=
      regularNativeSideExchange n (finRotate n i) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalHom _*_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalHom _*
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalHom
      _)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalHom _
  rw [←map_inv,←map_mul,←map_mul,regularSideExchangeLinear_rotation n hn i]

theorem regularPolygonPairingElement_rotation (n : ℕ) (hn : 4<n) (i : Fin n) :
    regularNativeRotation n*regularPolygonPairingElement n hn i*(regularNativeRotation n)⁻¹=
      regularPolygonPairingElement n hn (finRotate n i) := by
  let R:=regularNativeRotation n
  let L:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (regularCyclePolygon n hn) i
  let M:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (regularCyclePolygon n hn) (finRotate n i)
  have hR : R*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L*R⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry M:=
    regular_native_reflection_conjugation R L M (regularNativeRotation_line n hn i)
  unfold regularPolygonPairingElement
  calc
    R*(regularNativeSideExchange n i*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
      L)*R⁻¹=
      (R*regularNativeSideExchange n i*R⁻¹)*(R*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L*R⁻¹):=by group
    _=regularNativeSideExchange n (finRotate n i)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry M:=by
      rw [hR,regularNativeSideExchange_rotation n hn i]


theorem regularPolygonPairingElement_rotation_iterate (n : ℕ) (hn : 4<n)
    (j : ℕ) (i : Fin n) :
    regularNativeRotation n^j*regularPolygonPairingElement n hn i*(regularNativeRotation n^j)⁻¹=
      regularPolygonPairingElement n hn (((finRotate n)^[j]) i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    let R:=regularNativeRotation n
    calc
      R^(j+1)*regularPolygonPairingElement n hn i*(R^(j+1))⁻¹=
          R*(R^j*regularPolygonPairingElement n hn i*(R^j)⁻¹)*R⁻¹:=by
            rw [pow_succ']
            group
      _=R*regularPolygonPairingElement n hn (((finRotate n)^[j]) i)*R⁻¹:=by rw [ih]
      _=regularPolygonPairingElement n hn (((finRotate n)^[j+1]) i):=by
        rw [regularPolygonPairingElement_rotation,Function.iterate_succ_apply']

theorem regular_finRotate_iterate {n : ℕ} (hn : 0<n) (j : ℕ) :
    ((finRotate n)^[j]) ⟨0,hn⟩=⟨j%n,Nat.mod_lt _ hn⟩ := by
  have regularFinRotateNatNonzero : NeZero n:=⟨hn.ne'⟩
  induction j with
  | zero => apply Fin.ext;simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih,finRotate_apply]
    apply Fin.ext
    simp only [Fin.val_add,Fin.val_one']
    rw [Nat.add_mod_mod,Nat.mod_add_mod]

theorem regularCanonicalIndex_iterate_rotate (k : ℕ) (hk : 2≤k) (j : ℕ) :
    ((regularCanonicalIndex k hk)^[j]) ⟨0,by omega⟩=
      ((finRotate (4*k))^[j*(2*k+1)]) ⟨0,by omega⟩ := by
  rw [regularCanonicalIndex_iterate,regular_finRotate_iterate (by omega)]

def regularCanonicalRotation (k : ℕ) (hk : 2≤k) : ℍ ≃ᵢ ℍ:=
  (regularPolygonPairingElement (4*k) (by omega) ⟨0,by omega⟩)⁻¹*
    regularNativeRotation (4*k)^(2*k+1)

theorem regularCanonicalRotation_fixed_vertex (k : ℕ) (hk : 2≤k) :
    regularCanonicalRotation k hk
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega))
        (regularCyclePolygon_vertices_finite (by omega)) ⟨0,by omega⟩)=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega))
        (regularCyclePolygon_vertices_finite (by omega)) ⟨0,by omega⟩ := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let i : Fin (4*k):=⟨0,by omega⟩
  have hidx : ((finRotate (4*k))^[2*k+1]) i=regularCanonicalIndex k hk i := by
    rw [←show 1*(2*k+1)=2*k+1 by omega,←regularCanonicalIndex_iterate_rotate k hk 1]
    rfl
  have he : (regularNativeRotation (4*k)^(2*k+1)) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q
    hf i)=
      regularPolygonPairingElement (4*k) (by omega) i (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i) := by
    rw [regularNativeRotation_pow_vertex,regularPolygonPairingElement_vertex,
      hidx,←regularCanonicalIndex_eq_rotate_opposite]
  change (regularPolygonPairingElement (4*k) (by omega) i)⁻¹
    ((regularNativeRotation (4*k)^(2*k+1)) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf
      i))=_
  rw [he,IsometryEquiv.inv_apply_self]

def regularCanonicalWord (k : ℕ) (hk : 2≤k) : ℕ → (regularPolygonSidePairing k hk).Generated
  | 0=>1
  | j+1=>regularCanonicalWord k hk j*
      ((regularPolygonSidePairing k hk).generator
        ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (regularCyclePolygon (4*k) (by omega))
          (regularCyclePolygon_vertices_finite (by omega)))
            (((regularCanonicalIndex k hk)^[j]) ⟨0,by omega⟩)))⁻¹

theorem regularCanonicalWord_flag_state (k : ℕ) (hk : 2≤k) (j : ℕ) :
    let Q:=regularCyclePolygon (4*k) (by omega)
    let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
    let S:=regularPolygonSidePairing k hk
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j])
      (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf ⟨0,by omega⟩)=
      (regularCanonicalWord k hk j,
        _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf (((regularCanonicalIndex k hk)^[j]) ⟨0,by omega⟩)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply',ih,regularPolygonCanonicalStep,Function.iterate_succ_apply']
    rfl

theorem regularCanonicalWord_value (k : ℕ) (hk : 2≤k) (j : ℕ) :
    (regularCanonicalWord k hk j).val=
      (regularCanonicalRotation k hk)^j*(regularNativeRotation (4*k)^(j*(2*k+1)))⁻¹ := by
  let R:=regularNativeRotation (4*k)
  let G:=regularPolygonPairingElement (4*k) (by omega) ⟨0,by omega⟩
  let K:=regularCanonicalRotation k hk
  induction j with
  | zero => simp [regularCanonicalWord]
  | succ j ih =>
    have hpair : regularPolygonPairingElement (4*k) (by omega)
        (((regularCanonicalIndex k hk)^[j]) ⟨0,by omega⟩)=
        R^(j*(2*k+1))*G*(R^(j*(2*k+1)))⁻¹ := by
      rw [regularCanonicalIndex_iterate_rotate,←regularPolygonPairingElement_rotation_iterate]
    change (regularCanonicalWord k hk j).val*
      ((regularPolygonSidePairing k hk).element
        ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (regularCyclePolygon (4*k) (by omega))
          (regularCyclePolygon_vertices_finite (by omega)))
            (((regularCanonicalIndex k hk)^[j]) ⟨0,by omega⟩)))⁻¹=_
    rw [regularPolygonSidePairing_element_index,hpair,ih]
    change (K^j*(R^(j*(2*k+1)))⁻¹)*(R^(j*(2*k+1))*G*(R^(j*(2*k+1)))⁻¹)⁻¹=
      K^(j+1)*(R^((j+1)*(2*k+1)))⁻¹
    rw [Nat.add_mul,Nat.one_mul,pow_add,pow_succ]
    dsimp only [K,regularCanonicalRotation,G,R]
    group


theorem regularNativeRotation_origin (n : ℕ) : regularNativeRotation n UpperHalfPlane.I=UpperHalfPlane.I := by
  have hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I=0:=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap _ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I))=_
  rw [hz,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap_zero,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero]

theorem regular_origin_corner (n : ℕ) (hn : 4<n) (i : Fin n) :
    UpperHalfPlane.I∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay (regularCyclePolygon n hn)
        (regularCyclePolygon_vertices_finite hn) i)
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay (regularCyclePolygon n hn) (regularCyclePolygon_vertices_finite hn) i) := by
  let θ : Fin n → ℝ:=fun _=>regularCycleAngle n
  let d:=regularCycleRadius n hn
  let hθ : ∀i : Fin n,θ i∈Ico (0:ℝ) Real.pi:=
    fun _i=>⟨(regularCycleAngle_mem hn).1.le,(regularCycleAngle_mem hn).2⟩
  let S:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ (regularCycleRadius_pos
    hn) (regularCycleRadius_balance hn)
  let z:=regularCycleVertex n hn i
  have hz : S.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z:=Subtype.ext rfl
  change UpperHalfPlane.I∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior
    (S.toDiscPolygon.cornerRayPrev i z hz).toHalfPlane
    (S.toDiscPolygon.cornerRayNext i z hz).toHalfPlane
  rw [S.cornerRayPrev_eq i z hz,S.cornerRayNext_eq i z hz,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.cornerRayABAtA_toHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.cornerRayACAtA_toHalfPlane]
  apply (S.cornerTriangle i).finiteHalfPlaneCornerAtDiscA z hz |>.mem_interior_iff _ |>.mpr
  have hzero : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I=0:=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero]
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.halfPlaneCoordinate,hzero] using S.cornerTriangle_origin_coordinates i

theorem regular_native_vertex_ne_origin (n : ℕ) (hn : 4<n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon n hn) (regularCyclePolygon_vertices_finite hn) i≠UpperHalfPlane.I := by
  let Q:=regularCyclePolygon n hn
  let hf:=regularCyclePolygon_vertices_finite hn
  let R:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay Q hf i
  let U:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay Q hf i
  intro he
  have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior_subset_compl_union R U (regular_origin_corner n hn i)
  exact h (Or.inl (he ▸ R.start_mem))

theorem regular_corner_half_angle (n : ℕ) (hn : 4<n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay (regularCyclePolygon n hn)
        (regularCyclePolygon_vertices_finite hn) i)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon n hn)
        (regularCyclePolygon_vertices_finite hn) i)
        UpperHalfPlane.I (regular_native_vertex_ne_origin n hn i))=Real.pi/n := by
  let Q:=regularCyclePolygon n hn
  let hf:=regularCyclePolygon_vertices_finite hn
  let R:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay Q hf i
  let U:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay Q hf i
  let V:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i) UpperHalfPlane.I (regular_native_vertex_ne_origin n hn i)
  have hθ : Q.angle i≠Real.pi:=ne_of_lt (by
    rw [regularCyclePolygon_angle]
    exact (regularCycleAngle_mem hn).2)
  have hne : R.supportLine≠U.supportLine:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_vertex_rays_proper Q hf i hθ
  have hdist : R.supportLine.pointDist UpperHalfPlane.I=U.supportLine.pointDist UpperHalfPlane.I := by
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay_support,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay_support]
    have hline:=regularNativeRotation_line n hn ((finRotate n).symm i)
    rw [Equiv.apply_symm_apply] at hline
    have hd:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q ((finRotate n).symm
      i)).pointDist_isometry_image
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i) (regularNativeRotation
        n) (regularNativeRotation n).isometry hline UpperHalfPlane.I
    rw [regularNativeRotation_origin] at hd
    exact hd.symm
  have hb:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngle_equidistant_bisects R U hne (regular_native_vertex_ne_origin n hn i)
    (regular_origin_corner n hn i) hdist
  have ha:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_add_of_mem_proper R V U hne (regular_origin_corner n hn i)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _ _) (regular_native_vertex_ne_origin n hn
      i).symm
  have he:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_vertex_angle Q (regularCyclePolygon_isConvex
    hn) hf i hθ
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R U=Q.angle i at he
  rw [he,regularCyclePolygon_angle] at ha
  change regularCycleAngle n=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R V+_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure V U at ha
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R V=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure V U at hb
  unfold regularCycleAngle at ha
  rw [show 2*Real.pi/(n:ℝ)=2*(Real.pi/n) by ring] at ha
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R V=Real.pi/n
  linarith only [ha,hb]


theorem regular_corner_next_half_angle (n : ℕ) (hn : 4<n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay (regularCyclePolygon n hn)
        (regularCyclePolygon_vertices_finite hn) i)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon n hn)
        (regularCyclePolygon_vertices_finite hn) i)
        UpperHalfPlane.I (regular_native_vertex_ne_origin n hn i))=Real.pi/n := by
  let Q:=regularCyclePolygon n hn
  let hf:=regularCyclePolygon_vertices_finite hn
  let R:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay Q hf i
  let U:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay Q hf i
  let V:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i) UpperHalfPlane.I (regular_native_vertex_ne_origin n hn i)
  have hθ : Q.angle i≠Real.pi:=ne_of_lt (by
    rw [regularCyclePolygon_angle]
    exact (regularCycleAngle_mem hn).2)
  have ha:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_add_of_mem_proper R V U
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_vertex_rays_proper Q hf i hθ) (regular_origin_corner n
      hn i)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _ _) (regular_native_vertex_ne_origin n hn
      i).symm
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_vertex_angle Q (regularCyclePolygon_isConvex hn) hf i
    hθ,
    regularCyclePolygon_angle,regular_corner_half_angle n hn i] at ha
  change regularCycleAngle n=Real.pi/n+_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure V U at ha
  unfold regularCycleAngle at ha
  rw [show 2*Real.pi/(n:ℝ)=2*(Real.pi/n) by ring] at ha
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure U V=Real.pi/n
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm]
  linarith only [ha]

theorem regularCycleVertex_ne_zero (n : ℕ) (hn : 4<n) (i : Fin n) :
    (regularCycleVertex n hn i:ℂ)≠0 := by
  intro hz
  have he : regularCycleVertex n hn i=0:=Subtype.ext hz
  apply regular_native_vertex_ne_origin n hn i
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (regularCycleVertex n hn i)=_
  rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero]

theorem regular_direction_smul {z : ℂ} (hz : z≠0) (r : ℝ) (hr : 0<r) :
    _root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection ⟨r • z,smul_ne_zero hr.ne' hz⟩=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection ⟨z,hz⟩ := by
  apply Circle.ext
  change (r • z)/((‖r • z‖:ℝ):ℂ)=z/(‖z‖:ℂ)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,Complex.ofReal_mul,Complex.real_smul]
  field_simp [Complex.ofReal_ne_zero.mpr hr.ne',Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)]

theorem regularCycleVertex_direction (n : ℕ) (hn : 4<n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection ⟨(regularCycleVertex n hn
      i:ℂ),regularCycleVertex_ne_zero n hn i⟩=
      Circle.exp ((2*(i:ℝ)+1)*Real.pi/n) := by
  let z:=regularCycleVertex n hn i
  let q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate (regularCycleAngle
    n) (regularCycleRadius n hn)
  let a:=(2*(i:ℝ)+1)*Real.pi/n
  have hq : 0<q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate_pos
    ⟨(regularCycleAngle_mem hn).1.le,(regularCycleAngle_mem hn).2⟩ (regularCycleRadius_pos hn)
  obtain ⟨r,hr,he⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_positive_smul z
  have hunit : (Circle.exp a:ℂ)=_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit a:=by
    simp only [Circle.coe_exp,_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit,circleMap_zero,Complex.ofReal_one,one_mul]
  have hz : r • (z:ℂ)=q • (Circle.exp a:ℂ):=by
    rw [←he,hunit]
    exact regularCycleVertex_klein hn i
  have hd:=congrArg (fun w : {w : ℂ // w≠0}=>_root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection w)
    (show (⟨r • (z:ℂ),smul_ne_zero hr.ne' (regularCycleVertex_ne_zero n hn i)⟩ : {w : ℂ // w≠0})=
      ⟨q • (Circle.exp a:ℂ),smul_ne_zero hq.ne' (Circle.exp a).coe_ne_zero⟩ from Subtype.ext hz)
  rw [regular_direction_smul (regularCycleVertex_ne_zero n hn i) r hr] at hd
  exact hd.trans (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection_radial q hq (Circle.exp a))

def regularRadialLine (n : ℕ) (hn : 4<n) (i : Fin n) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine:=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough UpperHalfPlane.I
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon n hn)
      (regularCyclePolygon_vertices_finite hn) i)
    (regular_native_vertex_ne_origin n hn i).symm).supportLine

theorem regular_native_diameter_reflection (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (h0 : UpperHalfPlane.I∈L.carrier) (z : 𝔻)
    (hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z∈L.carrier) (hz0 : (z:ℂ)≠0) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap
        ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection ⟨(z:ℂ),hz0⟩)^2) true) := by
  let D:=L.toDiscLine
  let M:=_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection ⟨(z:ℂ),hz0⟩)^2) true
  have hD0 : (0:𝔻)∈D.carrier:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.mem_carrier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero]
    exact h0
  have hDz : z∈D.carrier:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.mem_carrier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane]
    exact hz
  have hc:=D.reflection_zero_direction hD0 z hDz hz0
  apply IsometryEquiv.ext
  intro w
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (L.reflection w)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap M (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w)))
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  have hh : (D.reflection (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w):ℂ)=M (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w:ℂ):=by
    simpa only [M,pow_two] using hc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w)
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (L.toDiscLine.toHalfPlane.reflection
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
    w))):ℂ)=M (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w:ℂ) at hh
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] at hh
  exact Subtype.ext hh

theorem regularRadialLine_reflection (n : ℕ) (hn : 4<n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (regularRadialLine n hn i)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap
        ((Circle.exp ((2*(i:ℝ)+1)*Real.pi/n))^2) true) := by
  let R:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough UpperHalfPlane.I
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon n hn)
      (regularCyclePolygon_vertices_finite hn) i)
    (regular_native_vertex_ne_origin n hn i).symm
  have hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (regularCycleVertex n hn
    i)∈R.supportLine.carrier:=
    R.subset_support (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _ _)
  have he:=regular_native_diameter_reflection R.supportLine R.start_mem_support
    (regularCycleVertex n hn i) hz (regularCycleVertex_ne_zero n hn i)
  rw [regularCycleVertex_direction n hn i] at he
  exact he

theorem regularSideExchange_rotation_halfturn (k : ℕ) (hk : 2≤k) :
    regularNativeSideExchange (4*k) ⟨0,by omega⟩ * regularNativeRotation (4*k)^(2*k+1)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (regularRadialLine (4*k) (by omega) ⟨0,by omega⟩) := by
  rw [regularRadialLine_reflection]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalHom (regularSideExchangeLinear (4*k) ⟨0,by omega⟩)*
    (regularNativeRotationCircleHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator
      (4*k)))^(2*k+1)=_
  rw [←map_pow]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalHom (regularSideExchangeLinear (4*k) ⟨0,by omega⟩)*
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator (4*k))^(2*k+1)) false)=_
  rw [←map_mul]
  apply congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalHom
  dsimp only [regularSideExchangeLinear]
  rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_mul]
  simp only [ite_true,Bool.true_xor]
  congr 1
  norm_num only [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator,_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod,Fin.val_zero,Nat.cast_zero]
  simp only [←Circle.exp_natCast_mul,←Circle.exp_neg,←Circle.exp_add]
  congr 1
  have hk0 : (k:ℝ)≠0:=by exact_mod_cast (show k≠0 by omega)
  push_cast
  field_simp
  ring


theorem regular_radialRay_support (n : ℕ) (hn : 4<n) (i : Fin n) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon n hn)
      (regularCyclePolygon_vertices_finite hn) i)
      UpperHalfPlane.I (regular_native_vertex_ne_origin n hn i)).supportLine=regularRadialLine n hn i := by
  let v:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon n
    hn) (regularCyclePolygon_vertices_finite hn) i
  let R:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough v UpperHalfPlane.I (regular_native_vertex_ne_origin n hn i)
  let U:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough UpperHalfPlane.I v (regular_native_vertex_ne_origin n hn i).symm
  exact R.supportLine.eq_of_two_points U.supportLine (regular_native_vertex_ne_origin n hn i)
    R.start_mem_support (R.subset_support (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _ _))
    (U.subset_support (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _ _)) U.start_mem_support

theorem regularCanonicalRotation_reflections (k : ℕ) (hk : 2≤k) :
    regularCanonicalRotation k hk=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (regularCyclePolygon (4*k) (by omega)) ⟨0,by omega⟩)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (regularRadialLine (4*k) (by omega) ⟨0,by omega⟩) := by
  let r:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (regularCyclePolygon (4*k) (by omega)) ⟨0,by omega⟩)
  let e:=regularNativeSideExchange (4*k) ⟨0,by omega⟩
  have hr : r⁻¹=r:=inv_eq_of_mul_eq_one_right (_root_.LowDimensionalTopology.Geometry.Fuchsian.halfPlaneLineReflectionIsometry_sq _)
  have he : e⁻¹=e:=inv_eq_of_mul_eq_one_right (regularNativeSideExchange_square _ _)
  unfold regularCanonicalRotation regularPolygonPairingElement
  change (e*r)⁻¹*regularNativeRotation (4*k)^(2*k+1)=_
  rw [mul_inv_rev,hr,he,mul_assoc,regularSideExchange_rotation_halfturn k hk]

theorem regularCanonicalRotation_order (k : ℕ) (hk : 2≤k) :
    orderOf (regularCanonicalRotation k hk)=4*k := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let i : Fin (4*k):=⟨0,by omega⟩
  let R:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay Q hf i
  let U:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay Q hf i
  let V:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i) UpperHalfPlane.I (regular_native_vertex_ne_origin (4*k) (by omega) i)
  have hne : U.supportLine≠V.supportLine:=by
    intro he
    have hI : UpperHalfPlane.I∈U.supportLine.carrier:=he.symm ▸ V.subset_support (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _ _)
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleSide_subset_compl_support U R (regular_origin_corner (4*k) (by omega) i).2 hI
  have hθ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure U V=Real.pi/(↑(4*k):ℝ):=
    regular_corner_next_half_angle (4*k) (by omega) i
  have ho:=_root_.LowDimensionalTopology.Geometry.Fuchsian.native_reflection_product_order_of_angle U V hne (4*k) (by omega) hθ
  change orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry U.supportLine*
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry V.supportLine)=4*k at ho
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay_support,regular_radialRay_support] at ho
  rw [regularCanonicalRotation_reflections]
  exact ho

theorem regularCanonicalRotation_pow (k : ℕ) (hk : 2≤k) :
    (regularCanonicalRotation k hk)^(4*k)=1 := by
  rw [←regularCanonicalRotation_order k hk]
  exact pow_orderOf_eq_one _

theorem regularCanonicalWord_full_turn (k : ℕ) (hk : 2≤k) :
    regularCanonicalWord k hk (4*k)=1 := by
  apply Subtype.ext
  change (regularCanonicalWord k hk (4*k)).val=1
  rw [regularCanonicalWord_value,regularCanonicalRotation_pow,one_mul,pow_mul,
    regularNativeRotation_pow (4*k) (by omega),one_pow,inv_one]

/-- The actual complete lifted flag walk returns with the identity copy word. -/
theorem regularPolygonCanonical_full_turn (k : ℕ) (hk : 2≤k) :
    let Q:=regularCyclePolygon (4*k) (by omega)
    let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
    let S:=regularPolygonSidePairing k hk
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[4*k])
      (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf ⟨0,by omega⟩)=
      (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf ⟨0,by omega⟩) := by
  dsimp only
  rw [regularCanonicalWord_flag_state,regularCanonicalWord_full_turn,regularCanonicalIndex_iterate]
  congr 2
  apply Fin.ext
  exact Nat.mul_mod_right (4*k) (2*k+1)


theorem regularPlanarRotation_unit_normal (n : ℕ) (hn : 4<n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) false
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (2*(i:ℝ)*Real.pi/n))=
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (2*((finRotate n i):ℝ)*Real.pi/n) := by
  have hgen : (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n:ℂ)=_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (2*Real.pi/n):=by
    simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator,_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod,Circle.coe_exp,
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit,circleMap_zero,Complex.ofReal_one,one_mul]
  rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_apply]
  simp only [Bool.false_eq_true,ite_false,hgen]
  have he (j : Fin n) : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*(j:ℝ)+1)*Real.pi/n)=
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (2*(j:ℝ)*Real.pi/n)*_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (Real.pi/n):=by
    rw [←regular_polygonAngleUnit_add]
    congr 1
    ring
  have hc:=regularCycleVertex_rotation_angle hn i
  rw [he i,he (finRotate n i)] at hc
  apply mul_right_cancel₀ (show _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (Real.pi/n)≠0 by
    intro hz
    have h:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_norm (Real.pi/n)
    rw [hz,norm_zero] at h
    norm_num at h)
  simpa only [mul_assoc] using hc

theorem regularPolygon_rotation_mem_interior (n : ℕ) (hn : 4<n) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (regularNativeRotation n z)∈(regularCyclePolygon n
      hn).interior ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z∈(regularCyclePolygon n hn).interior := by
  let θ : Fin n → ℝ:=fun _=>regularCycleAngle n
  let d:=regularCycleRadius n hn
  let hθ : ∀i : Fin n,θ i∈Ico (0:ℝ) Real.pi:=
    fun _=>⟨(regularCycleAngle_mem hn).1.le,(regularCycleAngle_mem hn).2⟩
  let L:=_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) false
  have hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (regularNativeRotation n z))=
      L (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)):=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap L (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))))=_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,regular_klein_orthogonal]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (regularNativeRotation n
    z)∈(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ
    (regularCycleRadius_pos hn) (regularCycleRadius_balance hn)).interior ↔
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z∈(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ
    (regularCycleRadius_pos hn) (regularCycleRadius_balance hn)).interior
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_interior]
  change (∀i : Fin n,inner ℝ (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (regularNativeRotation n z)))<Real.tanh d) ↔
    ∀i : Fin n,inner ℝ (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))<Real.tanh d
  have hN (i : Fin n) : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n i))=
      L (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i)):=by
    rw [regularCyclePolygon_normalAngle hn _ (finRotate n i).isLt.le,
      regularCyclePolygon_normalAngle hn _ i.isLt.le]
    exact (regularPlanarRotation_unit_normal n hn i).symm
  constructor
  · intro hz i
    have h:=hz (finRotate n i)
    rwa [hN,hK,L.inner_map_map] at h
  · intro hz i
    obtain ⟨j,rfl⟩:=(finRotate n).surjective i
    rw [hN,hK,L.inner_map_map]
    exact hz j

theorem regularPolygon_rotation_interior (n : ℕ) (hn : 4<n) :
    regularNativeRotation n '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹'
      (regularCyclePolygon n hn).interior)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (regularCyclePolygon n hn).interior := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact (regularPolygon_rotation_mem_interior n hn w).mpr hw
  · intro hz
    refine ⟨(regularNativeRotation n)⁻¹ z,?_,(regularNativeRotation n).apply_inv_self z⟩
    exact (regularPolygon_rotation_mem_interior n hn _).mp
      (by rwa [IsometryEquiv.apply_inv_self])

theorem regularPolygon_rotation_carrier (n : ℕ) (hn : 4<n) :
    regularNativeRotation n '' (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon
      (regularCyclePolygon n hn)
      (regularCyclePolygon_vertices_finite hn)).carrier=
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (regularCyclePolygon n hn) (regularCyclePolygon_vertices_finite hn)).carrier := by
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier]
  change (regularNativeRotation
    n).toHomeomorph '' closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹'
    (regularCyclePolygon n hn).interior)=_
  rw [(regularNativeRotation n).toHomeomorph.image_closure]
  change closure (regularNativeRotation n '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹'
    (regularCyclePolygon n hn).interior))=
    closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (regularCyclePolygon n hn).interior)
  rw [regularPolygon_rotation_interior]


local instance regularCycleDiscHyperbolicMetric : MetricSpace 𝔻:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric

theorem regular_native_finite_rotation_chart (f : ℍ≃ᵢℍ) (n : ℕ) (hn : 3≤n)
    (ho : orderOf f=n) (p : ℍ) (hp : f p=p) (e : ℍ≃ᵢ𝔻) (he : e p=0) :
    ∃u : Circle,orderOf u=n ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation e f=_root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom u := by
  let g:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation e f
  have hg0 : g 0=0:=by
    rw [←he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation_apply,hp]
  have hgo : orderOf g=n:=
    (orderOf_injective (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation e)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation_injective e) f).trans ho
  obtain ⟨u,hu|hu⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_zero_isometry_formula g g.isometry hg0
  · have hform : g=_root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom u:=by
      apply IsometryEquiv.ext
      intro z
      apply Subtype.ext
      exact (hu z).trans (_root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom_apply u z).symm
    refine ⟨u,?_,hform⟩
    have hco:=orderOf_injective _root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom _root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom_injective u
    rw [←hform] at hco
    exact hco.symm.trans hgo
  · have hg2 : g^2=1:=by
      apply IsometryEquiv.ext
      intro z
      apply Subtype.ext
      change (g (g z):ℂ)=(z:ℂ)
      rw [hu,hu,map_mul]
      have hunit : (u:ℂ)*conj (u:ℂ)=1:=by
        rw [←Circle.coe_inv_eq_conj,←Circle.coe_mul,mul_inv_cancel,Circle.coe_one]
      simp only [Complex.conj_conj,←mul_assoc,hunit,one_mul]
    have hd : n∣2:=by
      rw [←hgo]
      exact orderOf_dvd_of_pow_eq_one hg2
    have hl:=Nat.le_of_dvd (by decide : 0<2) hd
    omega

theorem regular_circle_primitive_pow_equiv (u : Circle) (n : ℕ) (hn : 0<n)
    (ho : orderOf u=n) :
    ∃σ : Fin n≃Fin n,∀i : Fin n,u^i.val=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n^(σ i).val := by
  classical
  have regularCyclePowNatNonzero : NeZero n:=⟨hn.ne'⟩
  have hu : IsPrimitiveRoot u n:=IsPrimitiveRoot.iff_orderOf.mpr ho
  have hg : IsPrimitiveRoot (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n:ℂ) n:=
    (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_isPrimitiveRoot n
      hn.ne').map_of_injective (f:=Circle.coeHom) Circle.coe_injective
  have hroot (i : Fin n) : (u^i.val:Circle)^n=1:=by
    rw [pow_right_comm,hu.pow_eq_one,one_pow]
  have hex (i : Fin n) : ∃j : Fin n,u^i.val=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n^j.val:=by
    have hr : ((u^i.val:Circle):ℂ)^n=1:=by
      rw [←Circle.coe_pow,hroot,Circle.coe_one]
    obtain ⟨j,hj,heq⟩:=hg.eq_pow_of_pow_eq_one hr
    refine ⟨⟨j,hj⟩,?_⟩
    apply Circle.coe_injective
    simpa only [Circle.coe_pow] using heq.symm
  let σ : Fin n→Fin n:=fun i=>(hex i).choose
  have hσ (i : Fin n) : u^i.val=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n^(σ
    i).val:=(hex i).choose_spec
  have hinj : Function.Injective σ:=by
    intro i j hij
    apply Fin.ext
    apply hu.pow_inj i.isLt j.isLt
    rw [hσ i,hσ j,hij]
  refine ⟨Equiv.ofBijective σ ⟨hinj,Finite.surjective_of_injective hinj⟩,hσ⟩


theorem regular_vertex_sector_chart (k : ℕ) (hk : 2≤k) :
    let Q:=regularCyclePolygon (4*k) (by omega)
    let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
    let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf ⟨0,by omega⟩
    ∃e : ℍ≃ᵢ𝔻, e p=0 ∧
      (∀z : ℍ,z∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay Q hf ⟨0,by omega⟩)
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay Q hf ⟨0,by omega⟩)) ↔
        (e z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector (4*k)) ∧
      ∃u : Circle,orderOf u=4*k ∧
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation e (regularCanonicalRotation k hk)=_root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom u := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let i : Fin (4*k):=⟨0,by omega⟩
  let R:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay Q hf i
  let U:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay Q hf i
  have hθ : Q.angle i≠Real.pi:=ne_of_lt (by
    rw [regularCyclePolygon_angle]
    exact (regularCycleAngle_mem (show 4<4*k by omega)).2)
  have hne : R.supportLine≠U.supportLine:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_vertex_rays_proper Q hf i hθ
  have ha : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R U=Real.pi/(↑(2*k):ℝ):=by
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_vertex_angle Q (regularCyclePolygon_isConvex (by omega)) hf i hθ,
      regularCyclePolygon_angle_fourk k hk i]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
  obtain ⟨e,he,hCone,_hGroup,_hPair⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertex_group_chart R U hne (2*k) (by omega) ha
  refine ⟨e,he,?_,regular_native_finite_rotation_chart (regularCanonicalRotation k hk) (4*k)
    (by omega) (regularCanonicalRotation_order k hk) _ (regularCanonicalRotation_fixed_vertex k hk) e he⟩
  intro z
  have hc:=hCone z
  change _ ↔ (e z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector (2*(2*k)) at hc
  simpa only [show 2*(2*k)=4*k by omega] using hc

theorem regular_circle_closed_sector_cover (u : Circle) (n : ℕ) (hn : 0<n)
    (ho : orderOf u=n) (y : 𝔻) :
    ∃i : Fin n,∃x : 𝔻,(x:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector n ∧
      _root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom (u^i.val) x=y := by
  obtain ⟨σ,hσ⟩:=regular_circle_primitive_pow_equiv u n hn ho
  have hy : (y:ℂ)∈⋃j : Fin n,(fun z : ℂ=>(_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator
    n^j.val:Circle)*z) ''
      _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector n:=by
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotation_closedPlaneSector_finite_cover n hn]
    trivial
  obtain ⟨j,x,hx,he⟩:=mem_iUnion.mp hy
  obtain ⟨i,rfl⟩:=σ.surjective j
  have hxnorm : ‖x‖<1:=by
    have hn:=congrArg norm he
    rw [norm_mul,Circle.norm_coe,one_mul] at hn
    exact hn ▸ y.norm_lt_one
  let z : 𝔻:=Complex.UnitDisc.mk x hxnorm
  refine ⟨i,z,hx,?_⟩
  apply Subtype.ext
  exact (_root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom_apply (u^i.val) z).trans
    ((congrArg (fun a : Circle=>(a:ℂ)*x) (hσ i)).trans he)

theorem regular_circle_open_sector_disjoint (u : Circle) (n : ℕ) (hn : 0<n)
    (ho : orderOf u=n) :
    Pairwise (fun i j : Fin n=>Disjoint
      ((_root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom (u^i.val)) '' {x : 𝔻 |
        (x:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n})
      ((_root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom (u^j.val)) '' {x : 𝔻 | (x:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n})) := by
  obtain ⟨σ,hσ⟩:=regular_circle_primitive_pow_equiv u n hn ho
  intro i j hij
  apply disjoint_left.mpr
  rintro z ⟨x,hx,hex⟩ ⟨y,hy,hey⟩
  have hdis:=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotation_openPlaneSector_finite_disjoint n hn (σ.injective.ne hij)
  have hx' : (z:ℂ)∈(fun w : ℂ=>(_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n^(σ
    i).val:Circle)*w) ''
      _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n:=by
    refine ⟨(x:ℂ),hx,?_⟩
    exact (congrArg (fun a : Circle=>(a:ℂ)*(x:ℂ)) (hσ i)).symm.trans
      ((_root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom_apply (u^i.val) x).symm.trans
        (congrArg (fun w : 𝔻=>(w:ℂ)) hex))
  have hy' : (z:ℂ)∈(fun w : ℂ=>(_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n^(σ
    j).val:Circle)*w) ''
      _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n:=by
    refine ⟨(y:ℂ),hy,?_⟩
    exact (congrArg (fun a : Circle=>(a:ℂ)*(y:ℂ)) (hσ j)).symm.trans
      ((_root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom_apply (u^j.val) y).symm.trans
        (congrArg (fun w : 𝔻=>(w:ℂ)) hey))
  exact disjoint_left.mp hdis hx' hy'


theorem regular_interior_germ_of_germ {X : Type*} [TopologicalSpace X]
    {A B : Set X} {x : X} (h : ∀ᶠy in 𝓝 x,y∈A ↔ y∈B) :
    ∀ᶠy in 𝓝 x,y∈interior A ↔ y∈interior B := by
  obtain ⟨U,hU,hOpen,hx⟩:=mem_nhds_iff.mp h
  filter_upwards [hOpen.mem_nhds hx] with y hy
  have hg : A =ᶠ[𝓝 y] B:=by
    filter_upwards [hOpen.mem_nhds hy] with z hz
    exact propext (hU hz)
  exact hg.mem_interior_iff

theorem regular_sector_interior (n : ℕ) (hn : 2≤n) :
    interior {z : 𝔻 | (z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector n}=
      {z : 𝔻 | (z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n} := by
  have hnon : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector n).Nonempty:=by
    obtain ⟨x,hx⟩:=finiteMobiusRotationDomain_nonempty n (by omega)
    exact ⟨_,hx⟩
  have he:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector_hConvex n
    hn).interior_closure_eq_of_isOpen
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector_isOpen n) hnon
  rw [finiteRotationDiscSector_closure n (by omega)] at he
  exact he

theorem regularPolygon_carrier_interior (n : ℕ) (hn : 4<n) :
    interior (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (regularCyclePolygon n hn)
      (regularCyclePolygon_vertices_finite hn)).carrier=
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (regularCyclePolygon n hn) (regularCyclePolygon_vertices_finite hn)).interior := by
  let Q:=regularCyclePolygon n hn
  have he:=(regularCyclePolygon_isConvex hn).interior_closure_eq_of_isOpen
    Q.interior_isOpen ⟨0,regularCyclePolygon_origin_mem hn⟩
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier]
  change interior (closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph ⁻¹'
    Q.interior))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph ⁻¹' Q.interior
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.preimage_closure,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.preimage_interior,he]

theorem regularPolygon_vertex_sector_germ (k : ℕ) (hk : 2≤k) :
    let Q:=regularCyclePolygon (4*k) (by omega)
    let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
    let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf ⟨0,by omega⟩
    ∃e : ℍ≃ᵢ𝔻, e p=0 ∧ ∃u : Circle,orderOf u=4*k ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation e (regularCanonicalRotation k
        hk)=_root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom u ∧
      ∃r : ℝ,0<r ∧ ∀z : ℍ,dist z p<r →
        (z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ↔ (e
          z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector (4*k)) ∧
        (z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior ↔ (e z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector (4*k)) := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf ⟨0,by omega⟩
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  obtain ⟨e,he0,hCone,u,hu,hue⟩:=regular_vertex_sector_chart k hk
  have hθ : Q.angle ⟨0,by omega⟩≠Real.pi:=ne_of_lt (by
    rw [regularCyclePolygon_angle]
    exact (regularCycleAngle_mem (show 4<4*k by omega)).2)
  obtain ⟨r,hr,hG⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_vertex_closed_angle_germ Q (regularCyclePolygon_isConvex (by omega)) hf
    ⟨0,by omega⟩ hθ
  have hclosed : ∀ᶠz in 𝓝 p,z∈P.carrier ↔ (e z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector (4*k):=by
    filter_upwards [Metric.ball_mem_nhds p hr] with z hz
    exact (hG z hz).trans (hCone z)
  have hopen:=regular_interior_germ_of_germ hclosed
  have heOpen : interior {z : ℍ | (e
    z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector (4*k)}=
      {z : ℍ | (e z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector (4*k)}:=by
    change interior (e.toHomeomorph ⁻¹' {z : 𝔻 |
      (z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector (4*k)})=_
    rw [←e.toHomeomorph.preimage_interior,regular_sector_interior (4*k) (by omega)]
    rfl
  have hopen' : ∀ᶠz in 𝓝 p,z∈P.interior ↔ (e z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector (4*k):=by
    filter_upwards [hopen] with z hz
    change z∈interior P.carrier ↔ z∈interior {w : ℍ | (e
      w:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector (4*k)} at hz
    rw [regularPolygon_carrier_interior,heOpen] at hz
    exact hz
  obtain ⟨s,hs,hB⟩:=Metric.eventually_nhds_iff_ball.mp (hclosed.and hopen')
  exact ⟨e,he0,u,hu,hue,s,hs,hB⟩


theorem regularCanonicalRotation_pow_fixed_vertex (k : ℕ) (hk : 2≤k) (j : ℕ) :
    ((regularCanonicalRotation k hk)^j)
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega))
        (regularCyclePolygon_vertices_finite (by omega)) ⟨0,by omega⟩)=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega))
        (regularCyclePolygon_vertices_finite (by omega)) ⟨0,by omega⟩ := by
  induction j with
  | zero=>rfl
  | succ j ih=>rw [pow_succ,IsometryEquiv.mul_apply,regularCanonicalRotation_fixed_vertex,ih]

theorem regularPolygon_vertex_rotation_ball_cover (k : ℕ) (hk : 2≤k) :
    let Q:=regularCyclePolygon (4*k) (by omega)
    let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
    let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf ⟨0,by omega⟩
    let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
    ∃r : ℝ,0<r ∧
      (⋃j : Fin (4*k),((regularCanonicalRotation k hk)^j.val) '' (P.carrier∩Metric.ball p r))=Metric.ball p r ∧
      Pairwise (fun i j : Fin (4*k)=>Disjoint
        (((regularCanonicalRotation k hk)^i.val) '' (P.interior∩Metric.ball p r))
        (((regularCanonicalRotation k hk)^j.val) '' (P.interior∩Metric.ball p r))) := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf ⟨0,by omega⟩
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let K:=regularCanonicalRotation k hk
  obtain ⟨e,he0,u,hu,hue,r,hr,hG⟩:=regularPolygon_vertex_sector_germ k hk
  have hpow (j : ℕ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation e (K^j)=_root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom (u^j):=by
    rw [map_pow,hue,map_pow]
  have hfix (j : ℕ) : (K^j) p=p:=regularCanonicalRotation_pow_fixed_vertex k hk j
  refine ⟨r,hr,?_,?_⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨j,w,⟨_,hw⟩,rfl⟩:=mem_iUnion.mp hz
      change dist ((K^j.val) w) p<r
      rw [←hfix j.val,(K^j.val).dist_eq]
      exact hw
    · intro hz
      obtain ⟨j,x,hx,hact⟩:=regular_circle_closed_sector_cover u (4*k) (by omega) hu (e z)
      let w:=e.symm x
      have hew : e w=x:=e.apply_symm_apply x
      have hwz : (K^j.val) w=z:=by
        apply e.injective
        rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation_apply e (K^j.val) w,hpow,hew,hact]
      have hwball : dist w p<r:=by
        rw [←(K^j.val).dist_eq,hwz,hfix]
        exact hz
      refine mem_iUnion.mpr ⟨j,w,⟨(hG w hwball).1.mpr ?_,hwball⟩,hwz⟩
      rwa [hew]
  · intro i j hij
    apply disjoint_left.mpr
    rintro z ⟨x,⟨hx,hxb⟩,hex⟩ ⟨y,⟨hy,hyb⟩,hey⟩
    have hEx : (e x:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector (4*k):=(hG x
      hxb).2.mp hx
    have hEy : (e y:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector (4*k):=(hG y
      hyb).2.mp hy
    have hx' : e z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom (u^i.val) ''
        {v : 𝔻 | (v:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector (4*k)}:=by
      refine ⟨e x,hEx,?_⟩
      rw [←hpow,_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation_apply,hex]
    have hy' : e z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.circleDiscRotationHom (u^j.val) ''
        {v : 𝔻 | (v:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector (4*k)}:=by
      refine ⟨e y,hEy,?_⟩
      rw [←hpow,_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation_apply,hey]
    exact disjoint_left.mp (regular_circle_open_sector_disjoint u (4*k) (by omega) hu hij) hx' hy'


theorem regular_native_power_image (R : ℍ≃ᵢℍ) (A : Set ℍ)
    (hA : R '' A=A) (j : ℕ) : (R^j) '' A=A := by
  induction j with
  | zero=>simp
  | succ j ih=>
    rw [pow_succ']
    change (fun x : ℍ=>R ((R^j) x)) '' A=A
    rw [←image_image,ih,hA]

theorem regularCanonical_piece_image (k : ℕ) (hk : 2≤k) (A : Set ℍ)
    (hA : regularNativeRotation (4*k) '' A=A) (r : ℝ) (j : ℕ) :
    let Q:=regularCyclePolygon (4*k) (by omega)
    let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
    (regularCanonicalWord k hk j).val ''
      (A∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (((regularCanonicalIndex k hk)^[j]) ⟨0,by omega⟩)) r)=
      ((regularCanonicalRotation k hk)^j) ''
        (A∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf ⟨0,by omega⟩) r) := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf ⟨0,by omega⟩
  let v:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (((regularCanonicalIndex k hk)^[j]) ⟨0,by omega⟩)
  let R:=regularNativeRotation (4*k)^(j*(2*k+1))
  let K:=regularCanonicalRotation k hk
  have hR : R '' A=A:=regular_native_power_image _ A hA _
  have hmem (z : ℍ) : R z∈A ↔ z∈A:=by
    have hh : R z∈R '' A ↔ z∈A:=R.injective.mem_set_image
    rwa [hR] at hh
  have hp : R p=v:=by
    rw [regularNativeRotation_pow_vertex,←regularCanonicalIndex_iterate_rotate k hk j]
  rw [regularCanonicalWord_value]
  change (K^j*R⁻¹) '' (A∩Metric.ball v r)=(K^j) '' (A∩Metric.ball p r)
  ext z
  constructor
  · rintro ⟨x,⟨hx,hxb⟩,rfl⟩
    refine ⟨R⁻¹ x,⟨?_,?_⟩,rfl⟩
    · apply (hmem _).mp
      rwa [R.apply_inv_self]
    · change dist (R⁻¹ x) p<r
      rw [←R.dist_eq,R.apply_inv_self,hp]
      exact hxb
  · rintro ⟨x,⟨hx,hxb⟩,rfl⟩
    refine ⟨R x,⟨(hmem x).mpr hx,?_⟩,?_⟩
    · change dist (R x) v<r
      rw [←hp,R.dist_eq]
      exact hxb
    · change (K^j) (R⁻¹ (R x))=(K^j) x
      rw [R.inv_apply_self]

theorem regularPolygon_canonical_ball_cycle_at_zero (k : ℕ) (hk : 2≤k) :
    let Q:=regularCyclePolygon (4*k) (by omega)
    let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
    let S:=regularPolygonSidePairing k hk
    let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf ⟨0,by omega⟩
    ∃r : ℝ,0<r ∧
      (⋃j : Fin (4*k),S.vertexCyclePiece
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
          (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j.val])
          (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf ⟨0,by omega⟩))) r)=Metric.ball p r ∧
      Pairwise (fun i j : Fin (4*k)=>Disjoint
        (S.vertexCycleInteriorPiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
          (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[i.val]) (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf ⟨0,by omega⟩))) r)
        (S.vertexCycleInteriorPiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
          (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j.val]) (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf ⟨0,by omega⟩))) r)) := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let S:=regularPolygonSidePairing k hk
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf ⟨0,by omega⟩
  obtain ⟨r,hr,hcov,hdis⟩:=regularPolygon_vertex_rotation_ball_cover k hk
  have hC (j : ℕ) : S.vertexCyclePiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
      (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j]) (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf ⟨0,by omega⟩))) r=
      ((regularCanonicalRotation k hk)^j) '' (P.carrier∩Metric.ball p r):=by
    rw [regularCanonicalWord_flag_state]
    exact regularCanonical_piece_image k hk P.carrier (regularPolygon_rotation_carrier _ (by omega)) r j
  have hI (j : ℕ) : S.vertexCycleInteriorPiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
      (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j]) (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf ⟨0,by omega⟩))) r=
      ((regularCanonicalRotation k hk)^j) '' (P.interior∩Metric.ball p r):=by
    rw [regularCanonicalWord_flag_state]
    exact regularCanonical_piece_image k hk P.interior (regularPolygon_rotation_interior _ (by omega)) r j
  refine ⟨r,hr,?_,?_⟩
  · exact (iUnion_congr (fun j : Fin (4*k)=>hC j.val)).trans hcov
  · intro i j hij
    exact (hI i.val).symm ▸ (hI j.val).symm ▸ hdis hij


def regularFlagTranslate {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m) (hf :
  ∀i,‖(Q.vertices i:ℂ)‖<1)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ)
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf))
    (g : S.Generated) (a : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf
      S) : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S:=
  (g*a.1,a.2)

theorem regularFlagTranslate_iterate {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m) (hf :
  ∀i,‖(Q.vertices i:ℂ)‖<1)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ)
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf))
    (g : S.Generated) (a : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S) (j : ℕ) :
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j]) (regularFlagTranslate
      Q hf S g a)=
      regularFlagTranslate Q hf S g (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j]) a) := by
  induction j with
  | zero=>rfl
  | succ j ih=>
    rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']
    apply Prod.ext
    · change (g*(((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j]) a).1)*
        (S.generator (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j])
          a).2.val.2)⁻¹=
        g*((((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j]) a).1*
          (S.generator (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j])
            a).2.val.2)⁻¹)
      exact mul_assoc _ _ _
    · rfl

theorem regularPolygon_canonical_rebase (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    let Q:=regularCyclePolygon (4*k) (by omega)
    let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
    let S:=regularPolygonSidePairing k hk
    ∃a : Fin (4*k), ((regularCanonicalIndex k hk)^[a.val]) ⟨0,by omega⟩=i ∧
      ∀j : ℕ,((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf
        S)^[j]) (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)=
        regularFlagTranslate Q hf S (regularCanonicalWord k hk a.val)⁻¹
          (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[(j+a.val)%(4*k)])
            (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf ⟨0,by omega⟩)) := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let S:=regularPolygonSidePairing k hk
  let T:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S
  let z : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S:=(1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf ⟨0,by omega⟩)
  obtain ⟨a,ha⟩:=regularCanonicalIndex_single_cycle k hk i
  have hperiod : Function.IsPeriodicPt T (4*k) z:=regularPolygonCanonical_full_turn k hk
  have hbase : (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)=
      regularFlagTranslate Q hf S (regularCanonicalWord k hk a.val)⁻¹ ((T^[a.val]) z):=by
    rw [regularCanonicalWord_flag_state,ha]
    change (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)=
      ((regularCanonicalWord k hk a.val)⁻¹*regularCanonicalWord k hk
        a.val,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)
    rw [inv_mul_cancel]
  refine ⟨a,ha,?_⟩
  intro j
  rw [hbase,regularFlagTranslate_iterate,←Function.iterate_add_apply,
    ←hperiod.iterate_mod_apply (j+a.val)]

theorem regularFlagTranslate_piece {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m) (hf :
  ∀i,‖(Q.vertices i:ℂ)‖<1)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ)
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf))
    (g : S.Generated) (a : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S) (r : ℝ) :
    S.vertexCyclePiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
      (regularFlagTranslate Q hf S g a)) r=
      g.val '' S.vertexCyclePiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S a) r := by
  change (fun z : ℍ=>g.val (a.1.val z)) '' _=g.val '' ((fun z : ℍ=>a.1.val z) '' _)
  rw [image_image]
  rfl

theorem regularFlagTranslate_interiorPiece {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon
  m) (hf : ∀i,‖(Q.vertices i:ℂ)‖<1)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ)
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf))
    (g : S.Generated) (a : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S) (r : ℝ) :
    S.vertexCycleInteriorPiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
      (regularFlagTranslate Q hf S g a)) r=
      g.val '' S.vertexCycleInteriorPiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S a) r := by
  change (fun z : ℍ=>g.val (a.1.val z)) '' _=g.val '' ((fun z : ℍ=>a.1.val z) '' _)
  rw [image_image]
  rfl


theorem regularCanonicalWord_evaluation (k : ℕ) (hk : 2≤k) (j : ℕ) :
    let Q:=regularCyclePolygon (4*k) (by omega)
    let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
    (regularCanonicalWord k hk j).val
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (((regularCanonicalIndex k hk)^[j]) ⟨0,by omega⟩))=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf ⟨0,by omega⟩ := by
  rw [regularCanonicalWord_value]
  change ((regularCanonicalRotation k hk)^j)
    ((regularNativeRotation (4*k)^(j*(2*k+1)))⁻¹
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex _ _ (((regularCanonicalIndex k hk)^[j]) ⟨0,by omega⟩)))=_
  rw [regularCanonicalIndex_iterate_rotate,←regularNativeRotation_pow_vertex,
    IsometryEquiv.inv_apply_self,regularCanonicalRotation_pow_fixed_vertex]

/-- The full original canonical vertex-cycle condition is derived for every original flag. -/
theorem regularPolygon_canonical_cycle_conditions (k : ℕ) (hk : 2≤k) :
    _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonCanonicalCycleConditions (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega)) (regularPolygonSidePairing k hk) := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let S:=regularPolygonSidePairing k hk
  let T:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S
  let z : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S:=(1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf ⟨0,by omega⟩)
  let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf ⟨0,by omega⟩
  have regularCanonicalCycleNatNonzero : NeZero (4*k):=⟨by omega⟩
  obtain ⟨r,hr,hcov,hdis⟩:=regularPolygon_canonical_ball_cycle_at_zero k hk
  intro i
  obtain ⟨a,ha,hrebase⟩:=regularPolygon_canonical_rebase k hk i
  let g : S.Generated:=(regularCanonicalWord k hk a.val)⁻¹
  let σ : Fin (4*k)≃Fin (4*k):=finCycle a
  have hσ (j : Fin (4*k)) : (σ j).val=(j.val+a.val)%(4*k):=rfl
  have hg : g.val p=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i:=by
    apply (regularCanonicalWord k hk a.val).val.injective
    change (regularCanonicalWord k hk a.val).val
      ((regularCanonicalWord k hk a.val).val⁻¹ p)=_
    rw [IsometryEquiv.apply_inv_self]
    simpa only [ha] using (regularCanonicalWord_evaluation k hk a.val).symm
  have hclose : (T^[4*k]) (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)=(1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i):=by
    have h0:=hrebase 0
    have hn:=hrebase (4*k)
    simp only [zero_add,Nat.mod_eq_of_lt a.isLt,Function.iterate_zero_apply] at h0
    rw [Nat.add_mod_left,Nat.mod_eq_of_lt a.isLt] at hn
    exact hn.trans h0.symm
  have hC (j : Fin (4*k)) : S.vertexCyclePiece
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[j.val])
        (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i))) r=
      g.val '' S.vertexCyclePiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[(σ j).val]) z)) r:=by
    rw [hrebase j.val,regularFlagTranslate_piece]
    exact congrArg (fun q : ℕ=>g.val '' S.vertexCyclePiece
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[q]) z)) r) (hσ j).symm
  have hI (j : Fin (4*k)) : S.vertexCycleInteriorPiece
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[j.val])
        (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i))) r=
      g.val '' S.vertexCycleInteriorPiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[(σ j).val]) z)) r:=by
    rw [hrebase j.val,regularFlagTranslate_interiorPiece]
    exact congrArg (fun q : ℕ=>g.val '' S.vertexCycleInteriorPiece
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[q]) z)) r) (hσ j).symm
  refine ⟨4*k-1,r,hr,?_,?_,?_⟩
  · simpa only [show 4*k-1+1=4*k by omega] using hclose
  · rw [show 4*k-1+1=4*k by omega]
    calc
      _=⋃j : Fin (4*k),g.val '' S.vertexCyclePiece
          (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[(σ j).val])
            z)) r:=iUnion_congr hC
      _=g.val '' (⋃j : Fin (4*k),S.vertexCyclePiece
          (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[(σ j).val])
            z)) r):=image_iUnion.symm
      _=g.val '' (⋃j : Fin (4*k),S.vertexCyclePiece
          (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[j.val]) z)) r):=
        congrArg (fun A : Set ℍ=>g.val '' A) (σ.surjective.iUnion_comp (fun j : Fin (4*k)=>S.vertexCyclePiece
          (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[j.val]) z)) r))
      _=g.val '' Metric.ball p r:=congrArg (fun A : Set ℍ=>g.val '' A) hcov
      _=Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i) r:=by rw [g.val.image_ball,hg]
  · rw [show 4*k-1+1=4*k by omega]
    intro j l hjl
    rw [hI j,hI l]
    exact disjoint_image_of_injective g.val.injective (hdis (σ.injective.ne hjl))


theorem regular_normal_circle_power (n : ℕ) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (2*(i:ℝ)*Real.pi/n)=(_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n^i.val:Circle) := by
  have he : _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n^i.val=Circle.exp (2*(i:ℝ)*Real.pi/n):=by
    unfold _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod
    rw [←Circle.exp_natCast_mul]
    congr 1
    ring
  rw [he]
  simp only [Circle.coe_exp,_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit,circleMap_zero,Complex.ofReal_one,one_mul]

theorem regularPlanarOrthogonal_normal_exists (n : ℕ) (hn : 0<n) (u : Circle) (b : Bool)
    (hu : u^n=1) (i : Fin n) :
    ∃j : Fin n,_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap u b (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (2*(i:ℝ)*Real.pi/n))=
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (2*(j:ℝ)*Real.pi/n) := by
  have regularNormalNatNonzero : NeZero n:=⟨hn.ne'⟩
  have hg : IsPrimitiveRoot (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n:ℂ) n:=
    (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_isPrimitiveRoot n
      hn.ne').map_of_injective (f:=Circle.coeHom) Circle.coe_injective
  have hun : (u:ℂ)^n=1:=by rw [←Circle.coe_pow,hu,Circle.coe_one]
  have hni : (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (2*(i:ℝ)*Real.pi/n))^n=1:=by
    rw [regular_normal_circle_power,←Circle.coe_pow,pow_right_comm,
      _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_pow n hn.ne',one_pow,Circle.coe_one]
  have hroot : (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap u b (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (2*(i:ℝ)*Real.pi/n)))^n=1:=by
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_apply,mul_pow,hun,one_mul]
    cases b
    · exact hni
    · simp only [ite_true,←map_pow,hni,map_one]
  obtain ⟨j,hj,he⟩:=hg.eq_pow_of_pow_eq_one hroot
  refine ⟨⟨j,hj⟩,?_⟩
  have hpow : (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n:ℂ)^j=
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (2*((⟨j,hj⟩ : Fin n):ℝ)*Real.pi/n):=by
    simpa only [Circle.coe_pow] using (regular_normal_circle_power n ⟨j,hj⟩).symm
  exact he.symm.trans hpow

theorem regularSideExchangeLinear_coefficient_pow (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    ((Circle.exp Real.pi)*(Circle.exp (2*((i:ℝ)+1)*Real.pi/(↑(4*k):ℝ)))^2)^(4*k)=1 := by
  have hk0 : (k:ℝ)≠0:=by exact_mod_cast (show k≠0 by omega)
  have hpi : (Circle.exp Real.pi)^2=1:=by
    rw [←Circle.exp_natCast_mul]
    exact Circle.exp_two_pi
  have hb : (Circle.exp (2*((i:ℝ)+1)*Real.pi/(↑(4*k):ℝ)))^(4*k)=1:=by
    rw [←Circle.exp_natCast_mul]
    calc
      Circle.exp ((↑(4*k):ℝ)*(2*((i:ℝ)+1)*Real.pi/(↑(4*k):ℝ)))=
          Circle.exp (((i.val:ℤ)+1)*(2*Real.pi)):=by
        congr 1
        push_cast
        field_simp
      _=1:=by simpa only [Int.cast_add,Int.cast_natCast,Int.cast_one] using
        Circle.exp_int_mul_two_pi ((i.val:ℤ)+1)
  rw [mul_pow,pow_right_comm,hb,one_pow,mul_one,
    show 4*k=2*(2*k) by omega,pow_mul,hpi,one_pow]

theorem regularNativeSideExchange_mem_interior (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (regularNativeSideExchange (4*k) i z)∈(regularCyclePolygon (4*k) (by omega)).interior ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z∈(regularCyclePolygon (4*k) (by omega)).interior := by
  let n:=4*k
  let hn : 4<n:=by dsimp only [n];omega
  let θ : Fin n → ℝ:=fun _=>regularCycleAngle n
  let d:=regularCycleRadius n hn
  let hθ : ∀j : Fin n,θ j∈Ico (0:ℝ) Real.pi:=
    fun _=>⟨(regularCycleAngle_mem hn).1.le,(regularCycleAngle_mem hn).2⟩
  let L:=regularSideExchangeLinear n i
  let μ:=regularNativeSideExchange n i
  have hN (j : Fin n) : ∃l : Fin n,L (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d j))=
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d l):=by
    obtain ⟨l,hl⟩:=regularPlanarOrthogonal_normal_exists (4*k) (by omega)
      ((Circle.exp Real.pi)*(Circle.exp (2*((i:ℝ)+1)*Real.pi/(↑(4*k):ℝ)))^2) true
      (regularSideExchangeLinear_coefficient_pow k hk i) j
    refine ⟨l,?_⟩
    rw [regularCyclePolygon_normalAngle hn _ j.isLt.le,regularCyclePolygon_normalAngle hn _ l.isLt.le]
    exact hl
  have hforward (w : ℍ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (μ w)∈(regularCyclePolygon n
    hn).interior →
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w∈(regularCyclePolygon n hn).interior:=by
    have hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (μ w))=L (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w)):=by
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap L (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w))))=_
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,regular_klein_orthogonal]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (μ
      w)∈(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ
      (regularCycleRadius_pos hn) (regularCycleRadius_balance hn)).interior →
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w∈(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ
      (regularCycleRadius_pos hn) (regularCycleRadius_balance hn)).interior
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_interior]
    intro hw j
    obtain ⟨l,hl⟩:=hN j
    have h:=hw l
    rw [←hl,hK,L.inner_map_map] at h
    exact h
  constructor
  · exact hforward z
  · intro hz
    apply hforward (μ z)
    have hs : μ (μ z)=z:=congrArg (fun f : ℍ≃ᵢℍ=>f z) (regularNativeSideExchange_square n i)
    rwa [hs]

theorem regularNativeSideExchange_mem_carrier (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) (z : ℍ) :
    regularNativeSideExchange (4*k) i z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega))).carrier ↔
      z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega))).carrier := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let μ:=regularNativeSideExchange (4*k) i
  have hpre : μ.toHomeomorph ⁻¹' P.interior=P.interior:=by
    ext w
    exact regularNativeSideExchange_mem_interior k hk i w
  have he : μ.toHomeomorph ⁻¹' P.carrier=P.carrier:=by
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier,μ.toHomeomorph.preimage_closure,hpre]
  exact iff_of_eq (congrArg (fun A : Set ℍ=>z∈A) he)


theorem regularPolygon_opposite_side_neighborhoods (k : ℕ) (hk : 2≤k)
    (i : Fin (4*k)) (x : ℍ)
    (hx : x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (regularCyclePolygon (4*k) (by omega)) i)
    (hnot : x∉range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega)))) :
    (regularPolygonSidePairing k hk).OppositeSideNeighborhoods
      ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (regularCyclePolygon (4*k) (by omega))
        (regularCyclePolygon_vertices_finite (by omega))) i) x := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let S:=regularPolygonSidePairing k hk
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S₀:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePairing Q hf
  let s:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i
  let regularOppositeGeneratedIsometric : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  let regularMirrorGeneratedIsometric : IsIsometricSMul S₀.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  let p : P.Point:=⟨x,P.side_subset_carrier s hx⟩
  have ha (j : Fin (4*k)) : Q.angle j<Real.pi:=by
    rw [regularCyclePolygon_angle]
    exact (regularCycleAngle_mem (show 4<4*k by omega)).2
  obtain ⟨r,hstar⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_nonvertex_paired_side Q (regularCyclePolygon_isConvex (by omega))
    ha hf p i hx hnot
  have hOld : S₀.OppositeSideNeighborhoods s x:=hstar.oppositeSideNeighborhoods S₀
  apply (S.oppositeSideNeighborhoods_iff s x).mpr
  have hOld':= (S₀.oppositeSideNeighborhoods_iff s x).mp hOld
  have heq : P.carrier ∪ (fun z : ℍ=>S.generator s • z) ⁻¹' P.carrier=
      P.carrier ∪ (fun z : ℍ=>S₀.generator s • z) ⁻¹' P.carrier:=by
    apply congrArg (fun A : Set ℍ=>P.carrier∪A)
    ext z
    change S.element s z∈P.carrier ↔ S₀.element s z∈P.carrier
    rw [regularPolygonSidePairing_element_index,_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePairing_element]
    change regularNativeSideExchange (4*k) i
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i)) z)∈P.carrier ↔
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i)) z∈P.carrier
    exact regularNativeSideExchange_mem_carrier k hk i _
  rw [heq]
  exact hOld'

/-- All original Poincare side and full natural-cycle conditions are proved for the actual regular polygon. -/
theorem regularPolygon_native_fundamental (k : ℕ) (hk : 2≤k) :
    DiscreteTopology (regularPolygonSidePairing k hk).Generated ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (regularPolygonSidePairing k
        hk).Generated ℍ MeasureTheory.volume
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (regularCyclePolygon (4*k) (by omega)).interior) := by
  exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_poincare (regularCyclePolygon (4*k) (by omega))
    (regularCyclePolygon_vertices_finite (by omega)) (regularPolygonSidePairing k hk)
    (regularPolygon_opposite_side_neighborhoods k hk) (regularPolygon_canonical_cycle_conditions k hk)


/-- The normalized planar mirror is the reflection in a genuine native diameter. -/
theorem regular_unit_mirror_exists (u : Circle) :
    ∃L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine, _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (u^2) true) := by
  let z : 𝔻:=Complex.UnitDisc.mk (((1/2:ℝ):ℂ)*(u:ℂ)) (by
    rw [norm_mul,Circle.norm_coe,Complex.norm_real];norm_num)
  have hz : (z:ℂ)≠0:=mul_ne_zero (by norm_num) u.coe_ne_zero
  have hne : UpperHalfPlane.I≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z:=by
    intro he
    have he' : z=0:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective (he.symm.trans
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero.symm)
    exact hz (congrArg Subtype.val he')
  let R:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough UpperHalfPlane.I (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z) hne
  refine ⟨R.supportLine,?_⟩
  have hh:=regular_native_diameter_reflection R.supportLine R.start_mem_support z
    (R.subset_support (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _ _)) hz
  have hd : _root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection ⟨(z:ℂ),hz⟩=u:=by
    exact _root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection_radial (1/2) (by norm_num) u
  rwa [hd] at hh

/-- Every original opposite-side pairing is represented by a real determinant-one map. -/
theorem regularPolygonPairingElement_conformal (n : ℕ) (hn : 4<n) (i : Fin n) :
    regularPolygonPairingElement n hn i∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  let u:=Circle.exp (Real.pi/2+2*((i:ℝ)+1)*Real.pi/n)
  obtain ⟨L,hL⟩:=regular_unit_mirror_exists u
  have hu : u^2=Circle.exp Real.pi*(Circle.exp (2*((i:ℝ)+1)*Real.pi/n))^2:=by
    simp only [u,←Circle.exp_natCast_mul,←Circle.exp_add]
    congr 1
    ring
  have hμ : regularNativeSideExchange n i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L:=by
    rw [hL,hu]
    rfl
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (regularCyclePolygon n hn) i),?_⟩
  apply IsometryEquiv.ext
  intro z
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (regularCyclePolygon n hn) i)) • z=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action]
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L)
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (regularCyclePolygon n hn) i)) z)=_
  rw [←hμ]
  rfl

theorem regularPolygonGenerated_conformal (k : ℕ) (hk : 2≤k) :
    (regularPolygonSidePairing k hk).Generated≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨s,rfl⟩
  obtain ⟨i,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (regularCyclePolygon (4*k) (by omega))
    (regularCyclePolygon_vertices_finite (by omega))).surjective s
  rw [regularPolygonSidePairing_element_index]
  exact regularPolygonPairingElement_conformal (4*k) (by omega) i

def regularPolygonToMobius (k : ℕ) (hk : 2≤k) :
    (regularPolygonSidePairing k hk).Generated→*_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  _root_.LowDimensionalTopology.Geometry.Fuchsian.nativeConformalSubgroupMobiusHom _ (regularPolygonGenerated_conformal
    k hk)

def regularPolygonMobiusGroup (k : ℕ) (hk :
  2≤k) : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup:=
  (regularPolygonToMobius k hk).range

theorem regularPolygonHalfPlaneData (k : ℕ) (hk : 2≤k) :
    HalfPlaneFuchsianGroup (regularPolygonMobiusGroup k hk) := by
  let regularPolygonNativeDiscrete : DiscreteTopology (regularPolygonSidePairing k hk).Generated:=
    (regularPolygon_native_fundamental k hk).1
  exact nativeConformalSubgroup_halfPlaneData _ (regularPolygonGenerated_conformal k hk)

def regularPolygonGroupEquiv (k : ℕ) (hk : 2≤k) :
    (regularPolygonSidePairing k hk).Generated≃*regularPolygonMobiusGroup k hk:=
  MulEquiv.ofBijective (regularPolygonToMobius k hk).rangeRestrict
    ⟨fun _a _b h=> (_root_.LowDimensionalTopology.Geometry.Fuchsian.nativeConformalSubgroupMobiusHom_isometry _
      (regularPolygonGenerated_conformal k hk)).injective (congrArg Subtype.val h),
     (regularPolygonToMobius k hk).rangeRestrict_surjective⟩

theorem regularPolygonGroupEquiv_action (k : ℕ) (hk : 2≤k)
    (g : (regularPolygonSidePairing k hk).Generated) (z : ℍ) :
    letI :=(regularPolygonHalfPlaneData k hk).nativeAction
    regularPolygonGroupEquiv k hk g • z=g.val z := by
  let regularPolygonOriginalAction:=(regularPolygonHalfPlaneData k hk).nativeAction
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  rw [←(regularPolygonHalfPlaneData k hk).nativeAction_boundary]
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.nativeConformalSubgroupMobiusHom_action _ (regularPolygonGenerated_conformal k hk) g z

theorem regularPolygon_original_native_fundamental (k : ℕ) (hk : 2≤k) :
    letI :=(regularPolygonHalfPlaneData k hk).nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (regularPolygonMobiusGroup k
      hk) ℍ MeasureTheory.volume
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (regularCyclePolygon (4*k) (by omega)).interior) := by
  let regularPolygonOriginalAction:=(regularPolygonHalfPlaneData k hk).nativeAction
  let e:=regularPolygonGroupEquiv k hk
  have he (g : regularPolygonMobiusGroup k hk) (z : ℍ) :
      (Homeomorph.refl ℍ) (g • z)=e.symm g • (Homeomorph.refl ℍ) z:=by
    change g • z=(e.symm g).val z
    simpa only [e,MulEquiv.apply_symm_apply] using regularPolygonGroupEquiv_action k hk (e.symm g) z
  have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage e.symm (Homeomorph.refl ℍ) he
    (regularPolygon_native_fundamental k hk).2
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain _ ℍ (MeasureTheory.Measure.map
    id MeasureTheory.volume) (id ⁻¹' _) at h
  simpa only [MeasureTheory.Measure.map_id,preimage_id] using h


/-- Every whole-group incidence at the original vertex is one of the actual finite cycle copies. -/
theorem regularPolygon_native_vertex_preimages (k : ℕ) (hk : 2≤k)
    (g : (regularPolygonSidePairing k hk).Generated) (x : ℍ)
    (hx : x∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega))).carrier)
    (he : g.val x=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega)) ⟨0,by omega⟩) :
    ∃j : Fin (4*k),g=regularCanonicalWord k hk j.val ∧
      x=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega))
        (regularCyclePolygon_vertices_finite (by omega))
        (((regularCanonicalIndex k hk)^[j.val]) ⟨0,by omega⟩) := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S:=regularPolygonSidePairing k hk
  let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q hf ⟨0,by omega⟩
  let a : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S:=(1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf ⟨0,by omega⟩)
  let T:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S
  let C (j : Fin (4*k)) : S.Copy:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[j.val]) a)
  let regularVertexGeneratedIsometric : IsIsometricSMul S.Generated ℍ:=⟨fun h=>h.val.isometry⟩
  have hA:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_local_tessellation Q hf S
    (regularPolygon_opposite_side_neighborhoods k hk) (regularPolygon_canonical_cycle_conditions k hk)
  have hEval : Function.Injective S.evaluation:=
    (hA.covering_homeomorph_of_compact S
      (S.native_metric_assumptions
        (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isOpen Q hf)
        (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isConnected Q hf))
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q
        hf).le (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf)).2.injective
  have hn : 4*k-1+1=4*k:=by omega
  have hclose : ((T^[4*k-1+1]) a)=a:=by
    rw [hn]
    exact regularPolygonCanonical_full_turn k hk
  have hF : S.project ⁻¹' {S.project (1,p)}⊆range C:=by
    apply S.project_fiber_subset_of_step_closed (range C) (1,p) ⟨⟨0,by omega⟩,rfl⟩
    rintro _ ⟨j,rfl⟩ b hab
    rcases S.step_eq_or_sideMate (C j) b hab with h | ⟨s,hs,h⟩
    · exact h ▸ mem_range_self j
    · rw [h]
      have hh:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexCycle_incidence Q hf S a (4*k-1) hclose
        ⟨j.val,by omega⟩ s hs
      obtain ⟨l,hl⟩:=hh
      exact ⟨⟨l.val,by omega⟩,hl⟩
  have hp : S.project (g,⟨x,hx⟩)=S.project (1,p):=by
    apply hEval
    change g.val x=p.val
    exact he
  obtain ⟨j,hj⟩:=hF hp
  change _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[j.val])
    a)=(g,⟨x,hx⟩) at hj
  rw [regularCanonicalWord_flag_state] at hj
  exact ⟨j,(congrArg Prod.fst hj).symm,(congrArg (fun b : S.Copy=>b.2.val) hj).symm⟩

/-- The single genuine vertex cycle is accidental: its actual whole-group stabilizer is trivial. -/
theorem regularPolygon_native_vertex_free (k : ℕ) (hk : 2≤k)
    (g : (regularPolygonSidePairing k hk).Generated)
    (he : g.val (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega)) ⟨0,by omega⟩)=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega))
        (regularCyclePolygon_vertices_finite (by omega)) ⟨0,by omega⟩) : g=1 := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let σ (j : Fin (4*k)):=((regularCanonicalIndex k hk)^[j.val]) ⟨0,by omega⟩
  have hσ : Function.Injective σ:=Finite.injective_iff_surjective.mpr (fun i=>
    regularCanonicalIndex_single_cycle k hk i)
  obtain ⟨j,hg,hj⟩:=regularPolygon_native_vertex_preimages k hk g _
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q hf ⟨0,by omega⟩).property he
  have hj0 : j=⟨0,by omega⟩:=hσ ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_injective Q hf) hj.symm)
  rw [hg,hj0]
  rfl

abbrev regularPolygonDiscData (k : ℕ) (hk : 2≤k):=(regularPolygonHalfPlaneData k hk).cayleyData

def regularPolygonDiscDomain (k : ℕ) (hk : 2≤k) :
    Set (regularPolygonDiscData k hk).domain.carrier:=
  (regularPolygonHalfPlaneData k hk).cayleyCoordinate ''
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (regularCyclePolygon (4*k) (by omega)).interior)

def regularPolygonDiscVertex (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    (regularPolygonDiscData k hk).domain.carrier:=
  (regularPolygonHalfPlaneData k hk).cayleyCoordinate
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega)) i)

def regularPolygonDiscGroupEquiv (k : ℕ) (hk : 2≤k) :
    (regularPolygonSidePairing k hk).Generated≃*
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (regularPolygonMobiusGroup k hk):=
  (regularPolygonGroupEquiv k hk).trans
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (regularPolygonMobiusGroup k hk))

theorem regularPolygonDiscCoordinate_equivariant (k : ℕ) (hk : 2≤k)
    (g : (regularPolygonSidePairing k hk).Generated) (z : ℍ) :
    (regularPolygonHalfPlaneData k hk).cayleyCoordinate (g.val z)=
      regularPolygonDiscGroupEquiv k hk g • (regularPolygonHalfPlaneData k hk).cayleyCoordinate z := by
  have h:=(regularPolygonHalfPlaneData k hk).cayleyCoordinate_equivariant (regularPolygonGroupEquiv k hk g) z
  rw [regularPolygonGroupEquiv_action] at h
  exact h

/-- The actual unit-disc Mobius group has the literal original regular polygon as a fundamental domain. -/
theorem regularPolygonDisc_fundamental (k : ℕ) (hk : 2≤k) :
    IsFuchsianFundamentalDomain (regularPolygonDiscData k hk) (regularPolygonDiscDomain k hk):=
  (regularPolygonHalfPlaneData k hk).cayley_fundamental (regularPolygon_original_native_fundamental k hk)

theorem regularPolygonDiscDomain_finite (k : ℕ) (hk : 2≤k) :
    (regularPolygonDiscData k hk).finiteCoordinate '' regularPolygonDiscDomain k hk=
      (regularCyclePolygon (4*k) (by omega)).interior := by
  rw [regularPolygonDiscDomain,image_image]
  have he : (fun z : ℍ=>(regularPolygonDiscData k hk).finiteCoordinate
      ((regularPolygonHalfPlaneData k hk).cayleyCoordinate z))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc:=by
    funext z
    exact (regularPolygonHalfPlaneData k hk).cayleyCoordinate_finite z
  rw [he]
  exact image_preimage_eq _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.surjective

theorem regularPolygonDiscVertex_finite (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    (regularPolygonDiscData k hk).finiteCoordinate (regularPolygonDiscVertex k hk i)=
      regularCycleVertex (4*k) (by omega) i := by
  rw [regularPolygonDiscVertex,(regularPolygonHalfPlaneData k hk).cayleyCoordinate_finite]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane _

/-- Every actual finite vertex of the genuine fundamental polygon has the exact sharp circumradius. -/
theorem regularPolygonDiscVertex_circumradius (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 ((regularPolygonDiscData k
      hk).finiteCoordinate
      (regularPolygonDiscVertex k hk i)))=
      (Real.cos (Real.pi/(4*k:ℕ))/Real.sin (Real.pi/(4*k:ℕ)))^2 := by
  rw [regularPolygonDiscVertex_finite]
  exact regularCyclePolygon_circumradius (by omega) i


/-- The actual whole-group closed-polygon orbit is exactly the original list of vertices. -/
theorem regularPolygon_native_cycle (k : ℕ) (hk : 2≤k) :
    {x : ℍ|x∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega))).carrier ∧
      x∈MulAction.orbit (regularPolygonSidePairing k hk).Generated
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega))
          (regularCyclePolygon_vertices_finite (by omega)) ⟨0,by omega⟩)}=
      range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega))
        (regularCyclePolygon_vertices_finite (by omega))) := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf ⟨0,by omega⟩
  ext x
  constructor
  · rintro ⟨hx,ho⟩
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp ho
    have he : g⁻¹.val x=p:=by
      change g.val.symm x=p
      rw [←hg]
      exact g.val.symm_apply_apply p
    obtain ⟨j,_,hj⟩:=regularPolygon_native_vertex_preimages k hk g⁻¹ x hx he
    exact ⟨_,hj.symm⟩
  · rintro ⟨i,rfl⟩
    refine ⟨(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q hf i).property,?_⟩
    obtain ⟨j,hj⟩:=regularCanonicalIndex_single_cycle k hk i
    have he:=regularCanonicalWord_evaluation k hk j.val
    rw [hj] at he
    refine MulAction.mem_orbit_iff.mpr ⟨(regularCanonicalWord k hk j.val)⁻¹,?_⟩
    change (regularCanonicalWord k hk
      j.val).val.symm p=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i
    apply (regularCanonicalWord k hk j.val).val.injective
    rw [IsometryEquiv.apply_symm_apply]
    exact he.symm

theorem regularPolygonDiscCoordinate_mem_orbit (k : ℕ) (hk : 2≤k) (z x : ℍ) :
    (regularPolygonHalfPlaneData k hk).cayleyCoordinate x∈
      MulAction.orbit (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (regularPolygonMobiusGroup k hk))
        ((regularPolygonHalfPlaneData k hk).cayleyCoordinate z) ↔
      x∈MulAction.orbit (regularPolygonSidePairing k hk).Generated z := by
  let e:=(regularPolygonHalfPlaneData k hk).cayleyCoordinate
  let E:=regularPolygonDiscGroupEquiv k hk
  constructor
  · intro hx
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp hx
    refine MulAction.mem_orbit_iff.mpr ⟨E.symm g,?_⟩
    apply e.injective
    change e ((E.symm g).val z)=e x
    rw [regularPolygonDiscCoordinate_equivariant,E.apply_symm_apply]
    exact hg
  · intro hx
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp hx
    refine MulAction.mem_orbit_iff.mpr ⟨E g,?_⟩
    exact (regularPolygonDiscCoordinate_equivariant k hk g z).symm.trans (congrArg e hg)

/-- The source's cycle is the actual original Mobius orbit intersected with the literal closed polygon. -/
theorem regularPolygonDisc_cycle (k : ℕ) (hk : 2≤k) :
    fuchsianPolygonCycle (regularPolygonDiscData k hk) (regularPolygonDiscDomain k hk)
      (regularPolygonDiscVertex k hk ⟨0,by omega⟩)=range (regularPolygonDiscVertex k hk) := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let e:=(regularPolygonHalfPlaneData k hk).cayleyCoordinate
  ext y
  obtain ⟨x,rfl⟩:=e.surjective y
  have hc : e x∈closure (regularPolygonDiscDomain k hk) ↔
      x∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier:=by
    rw [regularPolygonDiscDomain,←e.image_closure,e.injective.mem_set_image]
    change x∈closure (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior ↔ _
    rw [←_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier]
  change (e x∈closure (regularPolygonDiscDomain k hk) ∧
    e x∈MulAction.orbit _ (regularPolygonDiscVertex k hk ⟨0,by omega⟩)) ↔ _
  rw [hc]
  have ho:=regularPolygonDiscCoordinate_mem_orbit k hk (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf ⟨0,by omega⟩) x
  change e x∈MulAction.orbit _ (regularPolygonDiscVertex k hk ⟨0,by omega⟩) ↔ _ at ho
  rw [ho]
  change x∈{x : ℍ|x∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ∧
    x∈MulAction.orbit (regularPolygonSidePairing k hk).Generated (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf ⟨0,by omega⟩)} ↔ _
  rw [regularPolygon_native_cycle]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,hi⟩
    exact ⟨i,e.injective hi⟩

/-- No nonidentity original Mobius group element fixes the vertex of this accidental cycle. -/
theorem regularPolygonDisc_vertex_accidental (k : ℕ) (hk : 2≤k) :
    IsAccidentalFuchsianPoint (regularPolygonDiscData k hk)
      (regularPolygonDiscVertex k hk ⟨0,by omega⟩) := by
  rw [isAccidentalFuchsianPoint_iff_no_stabilizer]
  intro g hg
  let e:=(regularPolygonHalfPlaneData k hk).cayleyCoordinate
  let E:=regularPolygonDiscGroupEquiv k hk
  let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega))
    (regularCyclePolygon_vertices_finite (by omega)) ⟨0,by omega⟩
  have he : (E.symm g).val p=p:=by
    apply e.injective
    rw [regularPolygonDiscCoordinate_equivariant,E.apply_symm_apply]
    exact hg
  have hh:=regularPolygon_native_vertex_free k hk (E.symm g) he
  have h:=congrArg E hh
  simpa only [E.map_one,E.apply_symm_apply] using h

theorem regularPolygonDisc_all_vertices_accidental (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    IsAccidentalFuchsianPoint (regularPolygonDiscData k hk) (regularPolygonDiscVertex k hk i) := by
  have hi : regularPolygonDiscVertex k hk i∈fuchsianPolygonCycle (regularPolygonDiscData k hk)
      (regularPolygonDiscDomain k hk) (regularPolygonDiscVertex k hk ⟨0,by omega⟩):=by
    rw [regularPolygonDisc_cycle]
    exact mem_range_self i
  exact (isAccidentalFuchsianPoint_cycle_invariant _ _ _ _ hi).mpr
    (regularPolygonDisc_vertex_accidental k hk)

theorem regularPolygonDiscVertex_injective (k : ℕ) (hk : 2≤k) :
    Function.Injective (regularPolygonDiscVertex k hk):=
  (regularPolygonHalfPlaneData k hk).cayleyCoordinate.injective.comp
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_injective _ _)

theorem regularPolygonDisc_cycle_card (k : ℕ) (hk : 2≤k) :
    fuchsianPolygonCycleLength (regularPolygonDiscData k hk)
      (fuchsianPolygonCycle (regularPolygonDiscData k hk) (regularPolygonDiscDomain k hk)
        (regularPolygonDiscVertex k hk ⟨0,by omega⟩))=4*k := by
  rw [fuchsianPolygonCycleLength,regularPolygonDisc_cycle,
    Set.ncard_range_of_injective (regularPolygonDiscVertex_injective k hk)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_fin]


/-- The actual finite regular polygon has equal hyperbolic side lengths. -/
theorem regularPolygon_equal_sides (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (regularCycleVertex (4*k) (by omega) i)
      (regularCycleVertex (4*k) (by omega) (finRotate (4*k) i))=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (regularCycleVertex (4*k) (by omega) ⟨0,by omega⟩)
      (regularCycleVertex (4*k) (by omega) (finRotate (4*k) ⟨0,by omega⟩)) := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let R:=regularNativeRotation (4*k)
  let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf
  have hi : ((finRotate (4*k))^[i.val]) ⟨0,by omega⟩=i:=by
    rw [regular_finRotate_iterate (by omega)]
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have h0 : (R^i.val) (p ⟨0,by omega⟩)=p i:=by
    rw [regularNativeRotation_pow_vertex,hi]
  have h1 : (R^i.val) (p (finRotate (4*k) ⟨0,by omega⟩))=p (finRotate (4*k) i):=by
    have hp0 : p (finRotate (4*k) ⟨0,by omega⟩)=R (p ⟨0,by omega⟩):=
      (regularNativeRotation_vertex (4*k) (by omega) ⟨0,by omega⟩).symm
    rw [hp0]
    rw [←IsometryEquiv.mul_apply,←pow_succ,pow_succ',IsometryEquiv.mul_apply,h0]
    exact regularNativeRotation_vertex (4*k) (by omega) i
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]
  change dist (p i) (p (finRotate (4*k) i))=dist (p ⟨0,by omega⟩) (p (finRotate (4*k) ⟨0,by omega⟩))
  rw [←h0,←h1]
  exact (R^i.val).dist_eq _ _

/--
A genuine Fuchsian fundamental regular polygon, one actual accidental
vertex cycle, and equality in the stated circumradius bound for every integer k at least two.
-/
theorem regularPolygon_full_example (k : ℕ) (hk : 2≤k) :
    IsFuchsianFundamentalDomain (regularPolygonDiscData k hk) (regularPolygonDiscDomain k hk) ∧
    (regularPolygonDiscData k hk).finiteCoordinate '' regularPolygonDiscDomain k hk=
      (regularCyclePolygon (4*k) (by omega)).interior ∧
    Function.Injective (regularPolygonDiscVertex k hk) ∧
    fuchsianPolygonCycle (regularPolygonDiscData k hk) (regularPolygonDiscDomain k hk)
      (regularPolygonDiscVertex k hk ⟨0,by omega⟩)=range (regularPolygonDiscVertex k hk) ∧
    fuchsianPolygonCycleLength (regularPolygonDiscData k hk)
      (fuchsianPolygonCycle (regularPolygonDiscData k hk) (regularPolygonDiscDomain k hk)
        (regularPolygonDiscVertex k hk ⟨0,by omega⟩))=4*k ∧
    (∀i,IsAccidentalFuchsianPoint (regularPolygonDiscData k hk) (regularPolygonDiscVertex k hk i)) ∧
    (∀i,(regularCyclePolygon (4*k) (by omega)).angle i=Real.pi/(2*k)) ∧
    (∀i,Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 ((regularPolygonDiscData k
      hk).finiteCoordinate
      (regularPolygonDiscVertex k hk i)))=
      (Real.cos (Real.pi/(4*k:ℕ))/Real.sin (Real.pi/(4*k:ℕ)))^2) := by
  exact ⟨regularPolygonDisc_fundamental k hk,regularPolygonDiscDomain_finite k hk,
    regularPolygonDiscVertex_injective k hk,regularPolygonDisc_cycle k hk,
    regularPolygonDisc_cycle_card k hk,regularPolygonDisc_all_vertices_accidental k hk,
    regularCyclePolygon_angle_fourk k hk,regularPolygonDiscVertex_circumradius k hk⟩

end LowDimensionalTopology.Geometry.Fuchsian
