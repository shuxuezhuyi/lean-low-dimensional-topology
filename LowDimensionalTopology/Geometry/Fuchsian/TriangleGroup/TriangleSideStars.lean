module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincarePairedSideStars
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TrianglePoincareData
public import Mathlib.Tactic
@[expose] public section
noncomputable section
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
  Set
  InnerProductGeometry
open scoped UpperHalfPlane

def triangleBarycentric (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (z : ℍ) : Fin 3 → ℝ :=
  ![1-(T.coordinate z).1-(T.coordinate z).2,(T.coordinate z).1,(T.coordinate z).2]

def triangleOppositeVertex
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) : Fin 3 → ℍ := ![T.a,T.b,T.c]

theorem triangleBarycentric_continuous (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (i : Fin 3) :
    Continuous (fun z => triangleBarycentric T z i) := by
  have hc := T.coordinate_isOpenEmbedding.continuous
  fin_cases i
  · exact (continuous_const.sub hc.fst).sub hc.snd
  · exact hc.fst
  · exact hc.snd

theorem triangleBarycentric_sum (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (z : ℍ) :
    triangleBarycentric T z 0+triangleBarycentric T z 1+triangleBarycentric T z 2=1 := by
  simp [triangleBarycentric]
  ring

theorem triangleBarycentric_carrier (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (z : ℍ) :
    z ∈ (finiteTrianglePoincarePolygon T).carrier ↔ ∀ i,0 ≤ triangleBarycentric T z i := by
  rw [finiteTrianglePoincarePolygon_carrier,T.closure_coordinate_preimage]
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle,mem_preimage,mem_ofPred_eq]
  simp [triangleBarycentric,Fin.forall_fin_succ]
  constructor <;> intro h <;> rcases h with ⟨ha,hb,hc⟩ <;> constructor <;> try linarith
  all_goals constructor <;> linarith

theorem triangleBarycentric_sideLine
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (i : Fin 3)
    (z : ℍ) :
    z ∈ (finiteTrianglePoincareLine T i).carrier ↔ triangleBarycentric T z i=0 := by
  fin_cases i
  · change z ∈ T.sideLineA.carrier ↔ 1-(T.coordinate z).1-(T.coordinate z).2=0
    rw [T.sideLineA_iff_coordinate]
    constructor <;> intro h <;> linarith
  · exact T.sideLineB_iff_coordinate z
  · exact T.sideLineC_iff_coordinate z

theorem triangleBarycentric_affine
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (n : ℂ)
    (t : ℝ)
    (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine n t z =
      triangleBarycentric T z 0*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine n t T.a+
      triangleBarycentric T z 1*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine n t T.b+
      triangleBarycentric T z 2*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine n t T.c := by
  unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine
  rw [T.inner_klein_reconstruction]
  simp [triangleBarycentric]
  ring

theorem triangleBarycentric_opposite (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (i j : Fin 3) :
    triangleBarycentric T (triangleOppositeVertex T i) j=if i=j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [triangleBarycentric,triangleOppositeVertex,T.coordinate_a,T.coordinate_b,T.coordinate_c]

theorem triangleSide_affine_factor
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (i : Fin 3)
    (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine (finiteTrianglePoincareLine T i).incenterNormal
      (finiteTrianglePoincareLine T i).incenterOffset z =
    triangleBarycentric T z i * _root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine (finiteTrianglePoincareLine T i).incenterNormal
      (finiteTrianglePoincareLine T i).incenterOffset (triangleOppositeVertex T i) := by
  let N := finiteTrianglePoincareLine T i
  have hzero (j : Fin 3) (hij : i ≠ j) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine N.incenterNormal N.incenterOffset
      (triangleOppositeVertex T j)=0 := by
    apply (N.incenter_affine_eq_zero_iff _).mpr
    apply (triangleBarycentric_sideLine T i _).mpr
    rw [triangleBarycentric_opposite]
    simp [Ne.symm hij]
  have ha := triangleBarycentric_affine T N.incenterNormal N.incenterOffset z
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine N.incenterNormal N.incenterOffset z =
    triangleBarycentric T z 0*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine N.incenterNormal N.incenterOffset (triangleOppositeVertex T 0)+
    triangleBarycentric T z 1*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine N.incenterNormal N.incenterOffset (triangleOppositeVertex T 1)+
    triangleBarycentric T z 2*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine N.incenterNormal N.incenterOffset (triangleOppositeVertex T 2) at ha
  fin_cases i
  · rw [hzero 1 (by decide),hzero 2 (by decide),mul_zero,mul_zero,add_zero,add_zero] at ha
    exact ha
  · rw [hzero 0 (by decide),hzero 2 (by decide),mul_zero,mul_zero,zero_add,add_zero] at ha
    exact ha
  · rw [hzero 0 (by decide),hzero 1 (by decide),mul_zero,mul_zero,zero_add,zero_add] at ha
    exact ha

theorem triangleBarycentric_side (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (i : Fin 3) (z : ℍ) :
    z ∈ finiteTrianglePoincareSide T i ↔
      z ∈ (finiteTrianglePoincarePolygon T).carrier ∧ triangleBarycentric T z i=0 := by
  constructor
  · intro hz
    exact ⟨(finiteTrianglePoincarePolygon T).side_subset_carrier
      (finiteTrianglePoincareSideEquiv T i) hz,
      (triangleBarycentric_sideLine T i z).mp (finiteTrianglePoincareSide_subset_line T i hz)⟩
  · rintro ⟨hz,hi⟩
    have hh := (triangleBarycentric_carrier T z).mp hz
    have h0 := hh 0
    have h1 := hh 1
    have h2 := hh 2
    fin_cases i
    · apply (T.mem_sideA_iff_coordinate z).mpr
      change 1-(T.coordinate z).1-(T.coordinate z).2=0 at hi
      exact ⟨h1,h2,by linarith⟩
    · change z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHSegment T.c T.a
      rw [T.mem_closedHSegment_iff_coordinate,T.coordinate_c,T.coordinate_a,
        segment_symm ℝ ((0,1) : ℝ×ℝ) (0,0),_root_.LowDimensionalTopology.Geometry.Hyperbolic.standard_second_axis_segment]
      exact ⟨hi,h2,by change 0 ≤ 1-(T.coordinate z).1-(T.coordinate z).2 at h0;change (T.coordinate z).1=0 at hi;linarith⟩
    · change z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHSegment T.a T.b
      rw [T.mem_closedHSegment_iff_coordinate, T.coordinate_a, T.coordinate_b,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.standard_first_axis_segment]
      exact ⟨h1,by change 0 ≤ 1-(T.coordinate z).1-(T.coordinate z).2 at h0;change (T.coordinate z).2=0 at hi;linarith,hi⟩

theorem triangleSide_affine_opposite_ne (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (i : Fin 3) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine (finiteTrianglePoincareLine T i).incenterNormal
      (finiteTrianglePoincareLine T i).incenterOffset (triangleOppositeVertex T i) ≠ 0 := by
  intro he
  have hc := (finiteTrianglePoincareLine T i).incenter_affine_eq_zero_iff (triangleOppositeVertex T i)
  have hb := (triangleBarycentric_sideLine T i _).mp (hc.mp he)
  simp only [triangleBarycentric_opposite,ite_true] at hb
  exact one_ne_zero hb

theorem triangleSide_signed_halfspace
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (i : Fin 3)
    (z : ℍ) :
    0 ≤ (-_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine (finiteTrianglePoincareLine T i).incenterNormal
      (finiteTrianglePoincareLine T i).incenterOffset (triangleOppositeVertex T i))*
      (finiteTrianglePoincareLine T i).normalTimeAt z ↔ 0 ≤ triangleBarycentric T z i := by
  let k := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine (finiteTrianglePoincareLine T i).incenterNormal
    (finiteTrianglePoincareLine T i).incenterOffset (triangleOppositeVertex T i)
  have hk : k ≠ 0 := triangleSide_affine_opposite_ne T i
  have hp : 0 < _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight z*k^2 := mul_pos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos z) (sq_pos_of_ne_zero hk)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalTimeAt_eq_affine,
    triangleSide_affine_factor T i z]
  change 0 ≤ -k*(-_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight z*(triangleBarycentric T z i*k)) ↔ _
  have he : -k*(-_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight z*(triangleBarycentric T z i*k))=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight z*k^2)*triangleBarycentric T z i := by ring
  rw [he]
  exact mul_nonneg_iff_of_pos_left hp

/-- At an actual nonvertex point of a finite triangle side all the other genuine barycentric cuts are strict. -/
theorem triangleBarycentric_pos_off_side
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (i : Fin 3)
    (x : ℍ)
    (hx : x ∈ finiteTrianglePoincareSide T i)
    (hv : ∀ k : Fin 3,x ≠ triangleOppositeVertex T k) :
    ∀ j : Fin 3,j ≠ i → 0 < triangleBarycentric T x j := by
  have hside := (triangleBarycentric_side T i x).mp hx
  have hn := (triangleBarycentric_carrier T x).mp hside.1
  intro j hji
  by_contra hneg
  have hj : triangleBarycentric T x j=0 := le_antisymm (not_lt.mp hneg) (hn j)
  have hi := hside.2
  fin_cases i <;> fin_cases j
  all_goals first
  | exact hji rfl
  | (apply hv 0
     apply T.coordinate_isOpenEmbedding.injective
     rw [show triangleOppositeVertex T 0=T.a from rfl,T.coordinate_a]
     ext <;> dsimp [triangleBarycentric] at hi hj ⊢ <;> linarith)
  | (apply hv 1
     apply T.coordinate_isOpenEmbedding.injective
     rw [show triangleOppositeVertex T 1=T.b from rfl,T.coordinate_b]
     ext <;> dsimp [triangleBarycentric] at hi hj ⊢ <;> linarith)
  | (apply hv 2
     apply T.coordinate_isOpenEmbedding.injective
     rw [show triangleOppositeVertex T 2=T.c from rfl,T.coordinate_c]
     ext <;> dsimp [triangleBarycentric] at hi hj ⊢ <;> linarith)

/-- A sufficiently small actual native ball at a nonvertex side point misses every other side cut. -/
theorem triangleSide_exists_strict_ball
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (i : Fin 3)
    (x : ℍ)
    (hx : x ∈ finiteTrianglePoincareSide T i)
    (hv : ∀ k : Fin 3,x ≠ triangleOppositeVertex T k) :
    ∃ r : ℝ,0 < r ∧ ∀ z : ℍ,dist z x < r →
      ∀ j : Fin 3,j ≠ i → 0 < triangleBarycentric T z j := by
  let U : Set ℍ := ⋂ j : Fin 3,if j=i then univ else {z | 0 < triangleBarycentric T z j}
  have ho : IsOpen U := isOpen_iInter_of_finite (fun j => by
    split_ifs
    · exact isOpen_univ
    · exact isOpen_lt continuous_const (triangleBarycentric_continuous T j))
  have hxU : x ∈ U := by
    apply mem_iInter.mpr
    intro j
    split_ifs with he
    · exact mem_univ _
    · exact triangleBarycentric_pos_off_side T i x hx hv j he
  obtain ⟨r,hr,hU⟩ := Metric.isOpen_iff.mp ho x hxU
  refine ⟨r,hr,?_⟩
  intro z hz j hji
  have hj := mem_iInter.mp (hU hz) j
  simpa [hji] using hj

/-- Actual finite triangle side interiors have genuine reflected half-ball germs,
proved from the original triangle coordinates and its literal side reflection. -/
theorem finiteTriangle_nonvertex_side_neighborhood
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (i : Fin 3)
    (x : ℍ)
    (hx : x ∈ finiteTrianglePoincareSide T i)
    (hv : ∀ k : Fin 3,x ≠ triangleOppositeVertex T k) :
    ∃ r : ℝ,(finiteTrianglePoincarePairing T).PairedSideNeighborhood
      ⟨x,(triangleBarycentric_side T i x).mp hx |>.1⟩ (finiteTrianglePoincareSideEquiv T i) r := by
  let S := finiteTrianglePoincarePairing T
  let s := finiteTrianglePoincareSideEquiv T i
  let N := finiteTrianglePoincareLine T i
  let xp : (finiteTrianglePoincarePolygon T).Point := ⟨x,((triangleBarycentric_side T i x).mp hx).1⟩
  obtain ⟨r,hr,hB⟩ := triangleSide_exists_strict_ball T i x hx hv
  have hP : ∀ z : ℍ,dist z x < r →
      (z ∈ (finiteTrianglePoincarePolygon T).carrier ↔ 0 ≤ triangleBarycentric T z i) := by
    intro z hz
    rw [triangleBarycentric_carrier]
    constructor
    · intro hh
      exact hh i
    · intro hh j
      by_cases hji : j=i
      · simpa only [hji] using hh
      · exact (hB z hz j hji).le
  have ho : ∀ t : (finiteTrianglePoincarePolygon T).Side,∀ y ∈ t.val,
      dist y x < r → t=s := by
    intro t y hyt hy
    let j := (finiteTrianglePoincareSideEquiv T).symm t
    have hyj : y ∈ finiteTrianglePoincareSide T j := by
      rwa [finiteTrianglePoincareSideEquiv_symm]
    have hji : j=i := by
      by_contra hji
      exact (ne_of_gt (hB y hy j hji)) ((triangleBarycentric_side T j y).mp hyj).2
    apply (finiteTrianglePoincareSideEquiv T).symm.injective
    simpa only [s,Equiv.symm_apply_apply] using hji
  refine ⟨r,?_⟩
  apply S.pairedSideNeighborhood_of_halfPlaneReflection N hr
    (neg_ne_zero.mpr (triangleSide_affine_opposite_ne T i)) hx
    (finiteTrianglePoincareSide_subset_line T i) rfl
  · intro z
    change finiteTrianglePoincareElement T s z=N.reflection z
    simp only [finiteTrianglePoincareElement,s,Equiv.symm_apply_apply]
    rfl
  · exact ho
  · intro z hz
    exact (hP z hz).trans (triangleSide_signed_halfspace T i z).symm
  · intro z hz hzero
    apply (triangleBarycentric_side T i z).mpr
    have hline : z ∈ N.carrier := (N.normalTimeAt_eq_zero_iff z).mp hzero
    have hb := (triangleBarycentric_sideLine T i z).mp hline
    exact ⟨(hP z hz).mpr hb.ge,hb⟩

/-- The metric polygon hypotheses for the literal finite triangle and its three genuine side reflections. -/
theorem finiteTrianglePoincare_metric_assumptions (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    (finiteTrianglePoincarePairing T).MetricPolygonAssumptions := by
  refine ⟨fun s => (finiteTrianglePoincareElement T s).isometry,T.interior_isOpen,?_⟩
  exact ⟨T.interior_nonempty,T.interior_isPreconnected⟩

/--
Full original whole-fiber local tessellation holds at every original nonvertex point of a finite triangle;
only the actual finite vertex fan remains for the global condition.
-/
theorem finiteTriangle_nonvertex_local_condition (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (x : (finiteTrianglePoincarePolygon T).Point)
    (hv : ∀ k : Fin 3,x.val ≠ triangleOppositeVertex T k) :
    ((finiteTrianglePoincarePairing T).project ⁻¹'
      {(finiteTrianglePoincarePairing T).project (1,x)}).Finite ∧
    ∃ r₀ : ℝ,0 < r₀ ∧ ∀ r : ℝ,0 < r → r ≤ r₀ →
      (finiteTrianglePoincarePairing T).LocalTessellation (1,x) r := by
  let S := finiteTrianglePoincarePairing T
  let : IsIsometricSMul S.Generated ℍ := (finiteTrianglePoincare_metric_assumptions T).generatedIsometricSMul S
  have hx := x.property
  change x.val ∈ T.interior ∨ x.val ∈ ⋃₀(range (finiteTrianglePoincareSide T)) at hx
  rcases hx with hx | hx
  · constructor
    · rw [S.project_fiber_eq_singleton_of_interior (1,x) hx]
      exact Set.finite_singleton _
    · exact S.interior_local_radius T.interior_isOpen x hx
  · rcases hx with ⟨t,⟨i,rfl⟩,hx⟩
    obtain ⟨r,hr⟩ := finiteTriangle_nonvertex_side_neighborhood T i x.val hx hv
    exact ⟨hr.finite_class S,hr.local_radius S⟩

end LowDimensionalTopology.Geometry.Fuchsian
