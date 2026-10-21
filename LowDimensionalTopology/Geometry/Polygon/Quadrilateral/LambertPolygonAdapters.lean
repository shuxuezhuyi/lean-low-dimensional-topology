/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Support.CenteredDiscPolygonSupports
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.SaccheriQuadrilaterals
/-! # Actual Jordan polygons for the Lambert incidence model

The original finite/ideal incidence data determine actual supporting half-planes.
Their body is proved to be the union of two genuine triangular convex hulls.
This supplies an actual convex Jordan quadrilateral, with exact numerical angles
and the original true metric identities. The converse from an arbitrary Jordan
quadrilateral is a separate obligation.
-/
@[expose] public section
open Set InnerProductGeometry
open scoped Complex.UnitDisc Topology
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- The actual Euclidean normal representing a real linear functional on the complex plane. -/
def complexLinearFunctionalNormal (f : ℂ →ₗ[ℝ] ℝ) : ℂ := ⟨f 1,f Complex.I⟩

theorem complexLinearFunctionalNormal_inner (f : ℂ →ₗ[ℝ] ℝ) (z : ℂ) :
    inner ℝ (complexLinearFunctionalNormal f) z=f z := by
  have he : z=z.re • (1 : ℂ)+z.im • Complex.I := by apply Complex.ext <;> simp
  conv_rhs => rw [he]
  simp only [map_add,map_smul,smul_eq_mul,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,complexLinearFunctionalNormal]
  ring

/-- The first actual Klein-coordinate functional. -/
def _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.firstCoordinateFunctional (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) : ℂ →ₗ[ℝ] ℝ :=
  (LinearMap.fst ℝ ℝ ℝ).comp T.coordinateLinear.toLinearMap

def _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.secondCoordinateFunctional (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) : ℂ →ₗ[ℝ] ℝ :=
  (LinearMap.snd ℝ ℝ ℝ).comp T.coordinateLinear.toLinearMap

/-- Four actual successive vertices of the original convex Lambert configuration. -/
def LambertQuadrilateral.polygonVertices (Q : LambertQuadrilateral) : Fin 4 → 𝕔𝔻 :=
  ![Q.corner.a,Q.corner.b,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.a,Q.corner.c]

def LambertQuadrilateral.polygonRawFunctional (Q : LambertQuadrilateral) : Fin 4 → (ℂ →ₗ[ℝ] ℝ) :=
  let fx := Q.corner.firstCoordinateFunctional
  let fy := Q.corner.secondCoordinateFunctional
  let x := (Q.corner.discCoordinate Q.a).1
  let y := (Q.corner.discCoordinate Q.a).2
  ![-fy,y • fx-(x-1) • fy,(1-y) • fx+x • fy,-fx]

def LambertQuadrilateral.polygonRawConstant (Q : LambertQuadrilateral) : Fin 4 → ℝ :=
  ![0,(Q.corner.discCoordinate Q.a).2,(Q.corner.discCoordinate Q.a).1,0]

def LambertQuadrilateral.polygonRawOffset (Q : LambertQuadrilateral) (i : Fin 4) : ℝ :=
  Q.polygonRawFunctional i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    Q.corner.a)+Q.polygonRawConstant i

theorem LambertQuadrilateral.polygonRaw_evaluate_ambient (Q : LambertQuadrilateral) (i : Fin 4) (z : ℂ) :
    Q.polygonRawFunctional i z-Q.polygonRawOffset i=
      ![-(Q.corner.coordinateLinear (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        Q.corner.a)).2,
        (Q.corner.discCoordinate Q.a).2*(Q.corner.coordinateLinear
          (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate Q.corner.a)).1-
          ((Q.corner.discCoordinate Q.a).1-1)*(Q.corner.coordinateLinear
            (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
            Q.corner.a)).2-(Q.corner.discCoordinate Q.a).2,
        (1-(Q.corner.discCoordinate Q.a).2)*(Q.corner.coordinateLinear
          (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate Q.corner.a)).1+
          (Q.corner.discCoordinate Q.a).1*(Q.corner.coordinateLinear
            (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
            Q.corner.a)).2-(Q.corner.discCoordinate Q.a).1,
        -(Q.corner.coordinateLinear (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate Q.corner.a)).1] i := by
  have hfx : Q.corner.firstCoordinateFunctional z-
      Q.corner.firstCoordinateFunctional (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate Q.corner.a)=(Q.corner.coordinateLinear (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate Q.corner.a)).1 := by
    change (Q.corner.coordinateLinear z).1-
      (Q.corner.coordinateLinear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        Q.corner.a)).1=
      (Q.corner.coordinateLinear (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        Q.corner.a)).1
    rw [map_sub]
    rfl
  have hfy : Q.corner.secondCoordinateFunctional z-
      Q.corner.secondCoordinateFunctional (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate Q.corner.a)=(Q.corner.coordinateLinear (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate Q.corner.a)).2 := by
    change (Q.corner.coordinateLinear z).2-
      (Q.corner.coordinateLinear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        Q.corner.a)).2=
      (Q.corner.coordinateLinear (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        Q.corner.a)).2
    rw [map_sub]
    rfl
  fin_cases i <;> simp only [LambertQuadrilateral.polygonRawFunctional,LambertQuadrilateral.polygonRawConstant,LambertQuadrilateral.polygonRawOffset,
    Matrix.cons_val_zero',Matrix.cons_val_succ',
    LinearMap.neg_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  · linear_combination -hfy
  · linear_combination (Q.corner.discCoordinate Q.a).2*hfx-((Q.corner.discCoordinate Q.a).1-1)*hfy
  · linear_combination (1-(Q.corner.discCoordinate Q.a).2)*hfx+(Q.corner.discCoordinate Q.a).1*hfy
  · linear_combination -hfx


theorem LambertQuadrilateral.polygonRaw_evaluate (Q : LambertQuadrilateral) (i : Fin 4) (p : 𝕔𝔻) :
    Q.polygonRawFunctional i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      p)-Q.polygonRawOffset i=
      ![-(Q.corner.coordinate p).2,
        (Q.corner.discCoordinate Q.a).2*(Q.corner.coordinate p).1-
          ((Q.corner.discCoordinate Q.a).1-1)*(Q.corner.coordinate p).2-(Q.corner.discCoordinate Q.a).2,
        (1-(Q.corner.discCoordinate Q.a).2)*(Q.corner.coordinate p).1+
          (Q.corner.discCoordinate Q.a).1*(Q.corner.coordinate p).2-(Q.corner.discCoordinate Q.a).1,
        -(Q.corner.coordinate p).1] i := Q.polygonRaw_evaluate_ambient i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)

theorem LambertQuadrilateral.polygonVertices_coordinates (Q : LambertQuadrilateral) (i : Fin 4) :
    Q.corner.coordinate (Q.polygonVertices i)=
      ![(0,0),(1,0),Q.corner.discCoordinate Q.a,(0,1)] i := by
  fin_cases i <;> simp only [LambertQuadrilateral.polygonVertices,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Q.corner.coordinate_a,Q.corner.coordinate_b,Q.corner.coordinate_c]
  rfl

theorem LambertQuadrilateral.polygonVertices_injective (Q : LambertQuadrilateral) :
    Function.Injective Q.polygonVertices := by
  have hx := Q.convex_corner.1.ne'
  have hy := Q.convex_corner.2.ne'
  intro i j hij
  have he := congrArg Q.corner.coordinate hij
  rw [Q.polygonVertices_coordinates i,Q.polygonVertices_coordinates j] at he
  rcases hxy : Q.corner.discCoordinate Q.a with ⟨x,y⟩
  simp only [hxy] at hx hy he
  fin_cases i <;> fin_cases j <;> simp_all

theorem LambertQuadrilateral.polygonRaw_table (Q : LambertQuadrilateral) (i j : Fin 4) :
    Q.polygonRawFunctional i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.polygonVertices
      j))-Q.polygonRawOffset i=
      ![![0,0,-(Q.corner.discCoordinate Q.a).2,-1],
        ![-(Q.corner.discCoordinate Q.a).2,0,0,1-(Q.corner.discCoordinate Q.a).1-(Q.corner.discCoordinate Q.a).2],
        ![-(Q.corner.discCoordinate Q.a).1,1-(Q.corner.discCoordinate Q.a).1-(Q.corner.discCoordinate Q.a).2,0,0],
        ![0,-1,-(Q.corner.discCoordinate Q.a).1,0]] i j := by
  rw [Q.polygonRaw_evaluate,Q.polygonVertices_coordinates]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> ring

theorem LambertQuadrilateral.polygonRaw_incident (Q : LambertQuadrilateral) (i : Fin 4) :
    Q.polygonRawFunctional i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.polygonVertices
      i))=Q.polygonRawOffset i ∧
    Q.polygonRawFunctional i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.polygonVertices (finRotate 4 i)))=Q.polygonRawOffset i := by
  have hnxt : ∀ j : Fin 4,finRotate 4 j=j+1 := by decide
  constructor <;> apply sub_eq_zero.mp <;> rw [Q.polygonRaw_table] <;>
    (try rw [hnxt]) <;> fin_cases i <;> norm_num

theorem LambertQuadrilateral.polygonRaw_nonincident (Q : LambertQuadrilateral) (i j : Fin 4)
    (hji : j≠i) (hjnext : j≠finRotate 4 i) :
    Q.polygonRawFunctional i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.polygonVertices j))<Q.polygonRawOffset i := by
  apply sub_neg.mp
  rw [Q.polygonRaw_table]
  have hx := Q.convex_corner.1
  have hy := Q.convex_corner.2
  have hs := Q.opposite_chord
  have hnxt : ∀ k : Fin 4,finRotate 4 k=k+1 := by decide
  rw [hnxt] at hjnext
  fin_cases i <;> fin_cases j <;> norm_num at *
  all_goals linarith only [hx,hy,hs]

def LambertQuadrilateral.polygonCenter (Q : LambertQuadrilateral) : ℂ :=
  (1/4 : ℝ) • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.polygonVertices
    0)+_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.polygonVertices 1)+
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.polygonVertices
      2)+_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.polygonVertices 3))

theorem LambertQuadrilateral.polygonCenter_strict (Q : LambertQuadrilateral) (i : Fin 4) :
    Q.polygonRawFunctional i Q.polygonCenter<Q.polygonRawOffset i := by
  apply sub_neg.mp
  have hc : Q.polygonRawFunctional i Q.polygonCenter-Q.polygonRawOffset i=
      ((Q.polygonRawFunctional i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        (Q.polygonVertices 0))-Q.polygonRawOffset i)+
      (Q.polygonRawFunctional i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        (Q.polygonVertices 1))-Q.polygonRawOffset i)+
      (Q.polygonRawFunctional i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        (Q.polygonVertices 2))-Q.polygonRawOffset i)+
      (Q.polygonRawFunctional i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.polygonVertices 3))-Q.polygonRawOffset i))/4 := by
    simp only [LambertQuadrilateral.polygonCenter,map_smul,map_add,smul_eq_mul]
    ring
  rw [hc,Q.polygonRaw_table,Q.polygonRaw_table,Q.polygonRaw_table,Q.polygonRaw_table]
  have hx := Q.convex_corner.1
  have hy := Q.convex_corner.2
  have hs := Q.opposite_chord
  fin_cases i <;> norm_num
  all_goals linarith only [hx,hy,hs]

def LambertQuadrilateral.polygonRawNormal (Q : LambertQuadrilateral) (i : Fin 4) : ℂ :=
  complexLinearFunctionalNormal (Q.polygonRawFunctional i)

theorem LambertQuadrilateral.polygonRawNormal_ne_zero (Q : LambertQuadrilateral) (i : Fin 4) :
    Q.polygonRawNormal i≠0 := by
  intro hn
  have hf : ∀ z : ℂ,Q.polygonRawFunctional i z=0 := by
    intro z
    rw [← complexLinearFunctionalNormal_inner]
    change inner ℝ (Q.polygonRawNormal i) z=0
    rw [hn,inner_zero_left]
  have hi := (Q.polygonRaw_incident i).1
  rw [hf] at hi
  have hc := Q.polygonCenter_strict i
  rw [hf,← hi] at hc
  exact (lt_irrefl _ hc).elim

def LambertQuadrilateral.polygonUnitNormal (Q : LambertQuadrilateral) (i : Fin 4) : ℂ :=
  ‖Q.polygonRawNormal i‖⁻¹ • Q.polygonRawNormal i

def LambertQuadrilateral.polygonUnitOffset (Q : LambertQuadrilateral) (i : Fin 4) : ℝ :=
  Q.polygonRawOffset i/‖Q.polygonRawNormal i‖

theorem LambertQuadrilateral.polygonUnitNormal_norm (Q : LambertQuadrilateral) (i : Fin 4) :
    ‖Q.polygonUnitNormal i‖=1 := by
  have hn := norm_pos_iff.mpr (Q.polygonRawNormal_ne_zero i)
  rw [LambertQuadrilateral.polygonUnitNormal,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀
    hn.ne']

theorem LambertQuadrilateral.polygonUnit_le (Q : LambertQuadrilateral) (i : Fin 4) (z : ℂ) :
    inner ℝ (Q.polygonUnitNormal i) z≤Q.polygonUnitOffset i ↔
      Q.polygonRawFunctional i z≤Q.polygonRawOffset i := by
  rw [LambertQuadrilateral.polygonUnitNormal,real_inner_smul_left,LambertQuadrilateral.polygonRawNormal,complexLinearFunctionalNormal_inner,
    inv_mul_eq_div,LambertQuadrilateral.polygonUnitOffset]
  exact div_le_div_iff_of_pos_right (norm_pos_iff.mpr (Q.polygonRawNormal_ne_zero i))

theorem LambertQuadrilateral.polygonUnit_lt (Q : LambertQuadrilateral) (i : Fin 4) (z : ℂ) :
    inner ℝ (Q.polygonUnitNormal i) z<Q.polygonUnitOffset i ↔
      Q.polygonRawFunctional i z<Q.polygonRawOffset i := by
  rw [LambertQuadrilateral.polygonUnitNormal,real_inner_smul_left,LambertQuadrilateral.polygonRawNormal,complexLinearFunctionalNormal_inner,
    inv_mul_eq_div,LambertQuadrilateral.polygonUnitOffset]
  exact div_lt_div_iff_of_pos_right (norm_pos_iff.mpr (Q.polygonRawNormal_ne_zero i))

theorem LambertQuadrilateral.polygonUnit_eq (Q : LambertQuadrilateral) (i : Fin 4) (z : ℂ) :
    inner ℝ (Q.polygonUnitNormal i) z=Q.polygonUnitOffset i ↔
      Q.polygonRawFunctional i z=Q.polygonRawOffset i := by
  rw [le_antisymm_iff,Q.polygonUnit_le]
  have hle := Q.polygonUnit_le i z
  have hlt := Q.polygonUnit_lt i z
  exact ⟨fun h => le_antisymm h.1 (le_of_not_gt (fun hh => (not_lt_of_ge h.2) (hlt.mpr hh))),
    fun h => ⟨h.le,le_of_not_gt (fun hh => h.not_lt (hlt.mp hh))⟩⟩

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.klein_reconstruction_ambient (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (z : ℂ) :
    z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a+
      (T.coordinateLinear (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        T.a)).1 • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        T.b-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)+
      (T.coordinateLinear (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)).2 • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.c-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a) := by
  have he := T.kleinBasis.sum_repr (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)
  rw [Fin.sum_univ_two,T.kleinBasis_zero,T.kleinBasis_one] at he
  change (T.coordinateLinear (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    T.a)).1 • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    T.b-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)+
    (T.coordinateLinear (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      T.a)).2 • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      T.c-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)=
    z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a at he
  calc
    z = ((T.coordinateLinear (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)).1 •
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      T.b-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)+
      (T.coordinateLinear (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        T.a)).2 • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        T.c-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a))+
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a := sub_eq_iff_eq_add.mp he.symm
    _ = _ := by abel

theorem complex_closedBall_convex_combination_three (p q r : ℂ) (a b c : ℝ)
    (hp : p∈Metric.closedBall 0 1) (hq : q∈Metric.closedBall 0 1) (hr : r∈Metric.closedBall 0 1)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hs : a+b+c=1) :
    a • p+b • q+c • r∈Metric.closedBall (0 : ℂ) 1 := by
  have hp' : ‖a • p‖≤a := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp : ‖p‖≤1) ha
  have hq' : ‖b • q‖≤b := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hb]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hq : ‖q‖≤1) hb
  have hr' : ‖c • r‖≤c := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hr : ‖r‖≤1) hc
  change dist (a • p+b • q+c • r) 0≤1
  rw [dist_zero_right]
  linarith only [norm_add_le (a • p+b • q) (c • r),norm_add_le (a • p) (b • q),hp',hq',hr',hs]


theorem LambertQuadrilateral.polygonRaw_region_subset (Q : LambertQuadrilateral) :
    {z : ℂ | ∀ i,Q.polygonRawFunctional i z≤Q.polygonRawOffset i} ⊆ Metric.closedBall 0 1 := by
  intro z hz
  let T := Q.corner
  let u := (T.coordinateLinear (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)).1
  let v := (T.coordinateLinear (z-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)).2
  let x := (T.discCoordinate Q.a).1
  let y := (T.discCoordinate Q.a).2
  have hraw (i : Fin 4) := (Q.polygonRaw_evaluate_ambient i z).symm ▸ sub_nonpos.mpr (hz i)
  have hv0 : -v≤0 := hraw 0
  have hu0 : -u≤0 := hraw 3
  have he1 : y*u-(x-1)*v-y≤0 := hraw 1
  have he2 : (1-y)*u+x*v-x≤0 := hraw 2
  have hu : 0≤u := by linarith only [hu0]
  have hv : 0≤v := by linarith only [hv0]
  have hxy : 0<x+y-1 := by have h:=Q.opposite_chord;change 1<x+y at h;linarith only [h]
  have hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a∈Metric.closedBall (0 :
    ℂ) 1 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.range_closedKleinCoordinate ▸ mem_range_self T.a
  have hD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.b∈Metric.closedBall (0 :
    ℂ) 1 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.range_closedKleinCoordinate ▸ mem_range_self T.b
  have hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.c∈Metric.closedBall (0 :
    ℂ) 1 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.range_closedKleinCoordinate ▸ mem_range_self T.c
  have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.a)∈Metric.closedBall (0 : ℂ) 1 :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.range_closedKleinCoordinate ▸ mem_range_self (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.a)
  have hrec := T.klein_reconstruction_ambient z
  change z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a+u • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.b-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)+
    v • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      T.c-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a) at hrec
  by_cases hs : u+v≤1
  · have hcomb := complex_closedBall_convex_combination_three _ _ _ (1-u-v) u v hC hD hB
      (by linarith only [hs]) hu hv (by ring)
    have heq : (1-u-v) • _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a+u • _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.b+
        v • _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.c=z := by rw [hrec];module
    rwa [heq] at hcomb
  · let r := (u+v-1)/(x+y-1)
    have hr0 : 0≤r := div_nonneg (by linarith only [hs]) hxy.le
    have hr : r*(x+y-1)=u+v-1 := div_mul_cancel₀ _ hxy.ne'
    let a := u-r*x
    let c := v-r*y
    have ha : 0≤a := by
      apply nonneg_of_mul_nonneg_left (b:=x+y-1) ?_ hxy
      change 0≤(u-r*x)*(x+y-1)
      nlinarith only [he2,congrArg (fun t : ℝ => x*t) hr]
    have hc : 0≤c := by
      apply nonneg_of_mul_nonneg_left (b:=x+y-1) ?_ hxy
      change 0≤(v-r*y)*(x+y-1)
      nlinarith only [he1,congrArg (fun t : ℝ => y*t) hr]
    have hsum : a+r+c=1 := by dsimp [a,c];nlinarith only [hr]
    have hcomb := complex_closedBall_convex_combination_three _ _ _ a r c hD hA hB ha hr0 hc hsum
    have hrecA := T.klein_reconstruction (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.a)
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.a)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a+
      x • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        T.b-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)+
      y • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        T.c-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a) at hrecA
    have heq : a • _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.b+r • _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.a)+
        c • _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.c=z := by
      calc
        _ = (a+r+c) • _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a+(a+r*x) •
            (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
              T.b-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)+(c+r*y) •
            (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.c-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a) := by rw [hrecA];module
        _ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a+u • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.b-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)+
            v • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.c-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a) := by
          rw [hsum,one_smul,show a+r*x=u by dsimp [a];ring,show c+r*y=v by dsimp [c];ring]
        _ = z := hrec.symm
    rwa [heq] at hcomb

/-- The original geometric Lambert configuration supplies every genuine support hypothesis. -/
def LambertQuadrilateral.polygonSupportData (Q : LambertQuadrilateral) : CenteredDiscPolygonSupportData 4 where
  three_le := by norm_num
  vertices := Q.polygonVertices
  vertices_injective := Q.polygonVertices_injective
  normals := Q.polygonUnitNormal
  normal_norm := Q.polygonUnitNormal_norm
  offsets := Q.polygonUnitOffset
  center := Q.polygonCenter
  center_strict i := (Q.polygonUnit_lt i _).mpr (Q.polygonCenter_strict i)
  incident i := ⟨(Q.polygonUnit_eq i _).mpr (Q.polygonRaw_incident i).1,
    (Q.polygonUnit_eq i _).mpr (Q.polygonRaw_incident i).2⟩
  nonincident i j hji hjnext := (Q.polygonUnit_lt i _).mpr (Q.polygonRaw_nonincident i j hji hjnext)
  region_subset_closedBall z hz := Q.polygonRaw_region_subset (fun i => (Q.polygonUnit_le i z).mp (hz i))

/-- The original Lambert data now give an actual Jordan geodesic quadrilateral. -/
def LambertQuadrilateral.toDiscPolygon (Q : LambertQuadrilateral) : DiscPolygon 4 := Q.polygonSupportData.toDiscPolygon

theorem LambertQuadrilateral.toDiscPolygon_isConvex (Q : LambertQuadrilateral) : Q.toDiscPolygon.IsConvex :=
  Q.polygonSupportData.toDiscPolygon_isConvex


theorem LambertQuadrilateral.polygonSupportLine_eq (Q : LambertQuadrilateral) (i : Fin 4) :
    (Q.polygonSupportData.supportLine i)=![Q.corner.sideLineC,Q.left,Q.bottom,Q.corner.sideLineB] i := by
  let S := Q.polygonSupportData
  apply (S.supportLine i).eq_of_two_closed_points _
    (S.vertices_injective.ne (centeredPolygonSupport_next_ne_self S.three_le i).symm)
    (S.incident_mem_support i).1 (S.incident_mem_support i).2
  · fin_cases i
    · exact Q.corner.a_mem_sideLineC
    · change Q.corner.b∈Q.left.closedCarrier
      rw [Q.vertex_d]
      exact (Q.left.closedCarrier_mem_interior_iff Q.d).mpr Q.angle_d.1
    · exact (Q.bottom.closedCarrier_mem_interior_iff Q.a).mpr Q.angle_a.1
    · exact Q.corner.c_mem_sideLineB
  · have hnxt : ∀ j : Fin 4,finRotate 4 j=j+1 := by decide
    rw [hnxt]
    fin_cases i
    · exact Q.corner.b_mem_sideLineC
    · exact (Q.left.closedCarrier_mem_interior_iff Q.a).mpr Q.angle_a.2.1
    · change Q.corner.c∈Q.bottom.closedCarrier
      rw [Q.vertex_b]
      exact (Q.bottom.closedCarrier_mem_interior_iff Q.b).mpr Q.angle_b.1
    · exact Q.corner.a_mem_sideLineB

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.alpha_eq_of_swapped_neighbors (T U :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle)
    (ha : U.a=T.a) (hb : U.b=T.c) (hc : U.c=T.b) : U.alpha=T.alpha := by
  rcases _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDisc_interior_or_ideal T.a with ⟨z,hz⟩ | hz
  · have hT : T.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := hz.symm
    have hU : U.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := ha.trans hT
    have hTb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z≠T.b := hT ▸ T.a_ne_b
    have hTc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z≠T.c := hT ▸ T.c_ne_a.symm
    have hUb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z≠U.b := hb ▸ hTc
    have hUc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z≠U.c := hc ▸ hTb
    have hR : U.cornerRayABAtA z hU=T.cornerRayACAtA z hT := by
      rw [← U.rayToward_b z hU hUb,← T.rayToward_c z hT hTc]
      simp only [hb]
    have hS : U.cornerRayACAtA z hU=T.cornerRayABAtA z hT := by
      rw [← U.rayToward_c z hU hUc,← T.rayToward_b z hT hTb]
      simp only [hc]
    rw [U.alpha_of_finite z hU,T.alpha_of_finite z hT,hR,hS]
    exact angle_comm _ _
  · rw [U.alpha_of_ideal (by rw [ha];exact hz),T.alpha_of_ideal hz]

theorem LambertQuadrilateral.toDiscPolygon_angle_zero (Q : LambertQuadrilateral) :
    Q.toDiscPolygon.angle 0=Q.angle := by
  change Q.polygonSupportData.toDiscPolygon.angle 0=Q.corner.alpha
  rw [Q.polygonSupportData.angle_eq_cornerTriangle]
  apply Q.corner.alpha_eq_of_swapped_neighbors (Q.polygonSupportData.cornerTriangle 0) rfl
  · have hp : (finRotate 4).symm 0=(3 : Fin 4) := by decide
    change Q.polygonVertices ((finRotate 4).symm 0)=Q.corner.c
    rw [hp]
    rfl
  · rfl

theorem LambertQuadrilateral.toDiscPolygon_angle_one (Q : LambertQuadrilateral) :
    Q.toDiscPolygon.angle 1=Real.pi/2 := by
  change Q.polygonSupportData.toDiscPolygon.angle 1=Real.pi/2
  rw [Q.polygonSupportData.angle_eq_cornerTriangle]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.alpha_eq_pi_div_two_of_normalPairing_zero
  rw [Q.polygonSupportData.cornerTriangle_sideB,Q.polygonSupportData.cornerTriangle_sideC,
    Q.polygonSupportLine_eq,Q.polygonSupportLine_eq]
  have hp : (finRotate 4).symm 1=(0 : Fin 4) := by decide
  rw [hp]
  change Q.left.toHalfPlane.normalPairing Q.corner.sideLineC.toHalfPlane=0
  exact Q.left.toHalfPlane.normalPairing_orthogonal _ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
    Q.d)
    ((Q.left.orthogonalAt_iff_halfPlane Q.corner.sideLineC Q.d).mp Q.angle_d)

theorem LambertQuadrilateral.toDiscPolygon_angle_two (Q : LambertQuadrilateral) :
    Q.toDiscPolygon.angle 2=Real.pi/2 := by
  change Q.polygonSupportData.toDiscPolygon.angle 2=Real.pi/2
  rw [Q.polygonSupportData.angle_eq_cornerTriangle]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.alpha_eq_pi_div_two_of_normalPairing_zero
  rw [Q.polygonSupportData.cornerTriangle_sideB,Q.polygonSupportData.cornerTriangle_sideC,
    Q.polygonSupportLine_eq,Q.polygonSupportLine_eq]
  have hp : (finRotate 4).symm 2=(1 : Fin 4) := by decide
  rw [hp]
  change Q.bottom.toHalfPlane.normalPairing Q.left.toHalfPlane=0
  exact Q.bottom.toHalfPlane.normalPairing_orthogonal _ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.a)
    ((Q.bottom.orthogonalAt_iff_halfPlane Q.left Q.a).mp Q.angle_a)

theorem LambertQuadrilateral.toDiscPolygon_angle_three (Q : LambertQuadrilateral) :
    Q.toDiscPolygon.angle 3=Real.pi/2 := by
  change Q.polygonSupportData.toDiscPolygon.angle 3=Real.pi/2
  rw [Q.polygonSupportData.angle_eq_cornerTriangle]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.alpha_eq_pi_div_two_of_normalPairing_zero
  rw [Q.polygonSupportData.cornerTriangle_sideB,Q.polygonSupportData.cornerTriangle_sideC,
    Q.polygonSupportLine_eq,Q.polygonSupportLine_eq]
  have hp : (finRotate 4).symm 3=(2 : Fin 4) := by decide
  rw [hp]
  change Q.corner.sideLineB.toHalfPlane.normalPairing Q.bottom.toHalfPlane=0
  have hb := (Q.bottom.orthogonalAt_iff_halfPlane Q.corner.sideLineB Q.b).mp Q.angle_b
  exact Q.corner.sideLineB.toHalfPlane.normalPairing_orthogonal _ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.b)
    ⟨hb.2.1,hb.1,by rw [real_inner_comm];exact hb.2.2⟩

theorem LambertQuadrilateral.toDiscPolygon_angles (Q : LambertQuadrilateral) (i : Fin 4) :
    Q.toDiscPolygon.angle i=if i=0 then Q.angle else Real.pi/2 := by
  fin_cases i
  · exact Q.toDiscPolygon_angle_zero
  · exact Q.toDiscPolygon_angle_one
  · exact Q.toDiscPolygon_angle_two
  · exact Q.toDiscPolygon_angle_three


theorem exists_lambertDiscPolygon_angle (φ : ℝ) (hφ : φ∈Ico (0 : ℝ) (Real.pi/2)) :
    ∃ P : DiscPolygon 4,P.IsConvex ∧ P.angle 0=φ ∧ ∀ i : Fin 4,i≠0 → P.angle i=Real.pi/2 := by
  let Q := lambertQuadrilateralOfAngle φ hφ
  refine ⟨Q.toDiscPolygon,Q.toDiscPolygon_isConvex,?_,?_⟩
  · rw [Q.toDiscPolygon_angle_zero]
    exact lambertQuadrilateralOfAngle_angle φ hφ
  · intro i hi
    rw [Q.toDiscPolygon_angles,ite_eq_right hi]

theorem LambertQuadrilateral.toDiscPolygon_sinh_adjacent_mul_eq_cos_angle (Q : LambertQuadrilateral) :
    Real.sinh Q.sideA₁*Real.sinh Q.sideA₂=Real.cos (Q.toDiscPolygon.angle 0) := by
  rw [Q.toDiscPolygon_angle_zero]
  exact Q.sinh_adjacent_mul_eq_cos_angle

theorem LambertQuadrilateral.toDiscPolygon_cosh_side_eq_cosh_opposite_mul_sin (Q : LambertQuadrilateral) (z : 𝔻)
    (hz : Q.corner.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    Real.cosh Q.sideA₁=Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist Q.d z)*Real.sin (Q.toDiscPolygon.angle 0) := by
  rw [Q.toDiscPolygon_angle_zero]
  exact Q.cosh_side_eq_cosh_opposite_mul_sin z hz

end
end LowDimensionalTopology.Geometry.Polygon
