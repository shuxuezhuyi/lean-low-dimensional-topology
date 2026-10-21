/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletCyclicOrder
@[expose] public section
noncomputable section
open Set
open scoped Complex.UnitDisc BigOperators
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The oriented Euclidean determinant of actual circle points is computed
from their genuine principal arguments, including zero coordinates. -/
theorem cycle_complex_determinant (x y : ℂ) :
    x.re*y.im-x.im*y.re=‖x‖*‖y‖*Real.sin (y.arg-x.arg) := by
  rw [Real.sin_sub]
  calc
    x.re*y.im-x.im*y.re=
        (‖x‖*Real.cos x.arg)*(‖y‖*Real.sin y.arg)-
        (‖x‖*Real.sin x.arg)*(‖y‖*Real.cos y.arg):=by
      rw [Complex.norm_mul_cos_arg,Complex.norm_mul_sin_arg,
        Complex.norm_mul_sin_arg,Complex.norm_mul_cos_arg]
    _=‖x‖*‖y‖*(Real.sin y.arg*Real.cos x.arg-Real.cos y.arg*Real.sin x.arg):=by ring

/-- The wrap correction changes the genuine oriented gap by exactly one full turn. -/
theorem circleHalfArc_sin {n : ℕ} (a : Fin n→ℝ) (i : Fin n) :
    Real.sin (2*circleHalfArc a i)=Real.sin (a (finRotate n i)-a i) := by
  unfold circleHalfArc
  split_ifs with hi
  · rw [show 2*((a (finRotate n i)-a i+2*Real.pi)/2)=a (finRotate n i)-a i+2*Real.pi by ring]
    exact Real.sin_add_two_pi _
  · congr 1
    ring

/-- For actual equal-radius points, the determinant is the radius squared
times the sine of their actual cyclic angular gap. -/
theorem circleHalfArc_determinant {n : ℕ} (p : Fin n→Complex.UnitDisc)
    (R : ℝ) (hp : ∀i,‖(p i:ℂ)‖=R) (i : Fin n) :
    (p i:ℂ).re*(p (finRotate n i):ℂ).im-(p i:ℂ).im*(p (finRotate n i):ℂ).re=
      R^2*Real.sin (2*circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i) := by
  rw [cycle_complex_determinant,hp i,hp (finRotate n i),circleHalfArc_sin]
  ring

/-- A nonzero genuine Euclidean determinant excludes a shared native
geodesic through the origin, by its actual Klein affine equation. -/
def cycleTriangleAtZero (x y : Complex.UnitDisc)
    (hdet : (x:ℂ).re*(y:ℂ).im-(x:ℂ).im*(y:ℂ).re≠0) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscTriangle where
  a:=0
  b:=x
  c:=y
  noncollinear:=by
    rintro ⟨L,h0,hx,hy⟩
    obtain ⟨v,t,hv,hL⟩:=L.exists_klein_affine_equation
    have ht : t=0:=by
      have h:=(hL 0).mp h0
      simpa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula] using h.symm
    have hxn : inner ℝ (x:ℂ) v=0:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.klein_diameter_iff x v).mpr (by simpa only [ht,_root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein,Complex.UnitDisc.coe_mk] using (hL x).mp hx)
    have hyn : inner ℝ (y:ℂ) v=0:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.klein_diameter_iff y v).mpr (by simpa only [ht,_root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein,Complex.UnitDisc.coe_mk] using (hL y).mp hy)
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates] at hxn hyn
    have hre : v.re=0:=by
      have hh : v.re*((x:ℂ).re*(y:ℂ).im-(x:ℂ).im*(y:ℂ).re)=0:=by
        linear_combination (y:ℂ).im*hxn-(x:ℂ).im*hyn
      exact (mul_eq_zero.mp hh).resolve_right hdet
    have him : v.im=0:=by
      have hh : v.im*((x:ℂ).re*(y:ℂ).im-(x:ℂ).im*(y:ℂ).re)=0:=by
        linear_combination (x:ℂ).re*hyn-(y:ℂ).re*hxn
      exact (mul_eq_zero.mp hh).resolve_right hdet
    exact hv (Complex.ext hre him)

/-- Every acute actual cyclic gap constructs its actual noncollinear fan triangle. -/
def circleHalfArcTriangle {n : ℕ} (p : Fin n→Complex.UnitDisc) (R : ℝ)
    (hR : 0<R) (hp : ∀i,‖(p i:ℂ)‖=R) (i : Fin n)
    (hi : circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i∈Ioo (0:ℝ)
      (Real.pi/2)) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscTriangle:=
  cycleTriangleAtZero (p i) (p (finRotate n i)) (by
    rw [circleHalfArc_determinant p R hp i]
    exact mul_ne_zero (sq_pos_of_pos hR).ne' (Real.sin_pos_of_pos_of_lt_pi
      (by linarith only [hi.1]) (by linarith only [hi.2])).ne')

/-- At the actual native half-plane origin the genuine triangle angle is
the ordinary angle of the corresponding actual disc rays. -/
theorem cycle_halfPlane_apex_at_I (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (ha :
  T.a=UpperHalfPlane.I) :
    T.alpha=InnerProductGeometry.angle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc T.b:ℂ) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc T.c:ℂ) := by
  rcases T with ⟨a,b,c,hn⟩
  change a=UpperHalfPlane.I at ha
  subst a
  let T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle:=⟨UpperHalfPlane.I,b,c,hn⟩
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_I_cayley T.rayAB T.rayAC T.b_mem_rayAB T.a_ne_b.symm
    T.c_mem_rayAC T.c_ne_a

/-- The measured apex of every actual native disc triangle based at zero
agrees with the independently defined Euclidean ray angle. -/
theorem cycle_disc_apex_at_zero (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscTriangle) (ha : T.a=0) :
    T.alpha=InnerProductGeometry.angle (T.b:ℂ) (T.c:ℂ) := by
  rw [T.angles_eq_halfPlane.1,cycle_halfPlane_apex_at_I T.toHalfPlane (by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane T.a=UpperHalfPlane.I
    rw [ha,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero])]
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscTriangle.toHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]

/-- The Euclidean inner product uses the genuine principal-argument difference. -/
theorem cycle_complex_inner (x y : ℂ) :
    inner ℝ x y=‖x‖*‖y‖*Real.cos (y.arg-x.arg) := by
  rw [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,Real.cos_sub]
  calc
    x.re*y.re+x.im*y.im=
        (‖x‖*Real.cos x.arg)*(‖y‖*Real.cos y.arg)+
        (‖x‖*Real.sin x.arg)*(‖y‖*Real.sin y.arg):=by
      rw [Complex.norm_mul_cos_arg,Complex.norm_mul_cos_arg,
        Complex.norm_mul_sin_arg,Complex.norm_mul_sin_arg]
    _=‖x‖*‖y‖*(Real.cos y.arg*Real.cos x.arg+Real.sin y.arg*Real.sin x.arg):=by ring

theorem circleHalfArc_cos {n : ℕ} (a : Fin n→ℝ) (i : Fin n) :
    Real.cos (2*circleHalfArc a i)=Real.cos (a (finRotate n i)-a i) := by
  unfold circleHalfArc
  split_ifs with hi
  · rw [show 2*((a (finRotate n i)-a i+2*Real.pi)/2)=a (finRotate n i)-a i+2*Real.pi by ring]
    exact Real.cos_add_two_pi _
  · congr 1
    ring

/-- Every usable genuine cyclic gap is exactly the measured apex of its
actual native fan triangle. -/
theorem circleHalfArcTriangle_apex {n : ℕ} (p : Fin n→Complex.UnitDisc) (R : ℝ)
    (hR : 0<R) (hp : ∀i,‖(p i:ℂ)‖=R) (i : Fin n)
    (hi : circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i∈Ioo (0:ℝ) (Real.pi/2)) :
    (circleHalfArcTriangle p R hR hp i hi).alpha=
      2*circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i := by
  rw [cycle_disc_apex_at_zero _ rfl]
  change InnerProductGeometry.angle (p i:ℂ) (p (finRotate n i):ℂ)=_
  apply Real.injOn_cos ⟨InnerProductGeometry.angle_nonneg _ _,InnerProductGeometry.angle_le_pi _ _⟩
    ⟨by linarith only [hi.1],by linarith only [hi.2]⟩
  rw [InnerProductGeometry.cos_angle,cycle_complex_inner,hp i,hp (finRotate n i),circleHalfArc_cos]
  field_simp

/-- The fan triangle is genuinely isosceles because its actual vertices
have the same native radial distance. -/
theorem circleHalfArcTriangle_equal_sides {n : ℕ} (p : Fin n→Complex.UnitDisc) (R : ℝ)
    (hR : 0<R) (hp : ∀i,‖(p i:ℂ)‖=R) (i : Fin n)
    (hi : circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i∈Ioo (0:ℝ) (Real.pi/2)) :
    (circleHalfArcTriangle p R hR hp i hi).lengthB=
      (circleHalfArcTriangle p R hR hp i hi).lengthC := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (p (finRotate n
    i)) 0=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (p i)
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (p (finRotate n i)) 0=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (p (finRotate n i)):=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane,dist_comm]
  rw [hc]
  apply le_antisymm
  · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_distance_zero_le_of_norm_le (by rw [hp _,hp _])
  · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_distance_zero_le_of_norm_le (by rw [hp _,hp _])

/-- The true equal-radius fan triangle has a positive acute base angle. -/
theorem circleHalfArcTriangle_base_acute {n : ℕ} (p : Fin n→Complex.UnitDisc) (R : ℝ)
    (hR : 0<R) (hp : ∀i,‖(p i:ℂ)‖=R) (i : Fin n)
    (hi : circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i∈Ioo (0:ℝ) (Real.pi/2)) :
    (circleHalfArcTriangle p R hR hp i hi).beta∈Ioo (0:ℝ) (Real.pi/2) := by
  let T:=circleHalfArcTriangle p R hR hp i hi
  have he : T.toHalfPlane.lengthB=T.toHalfPlane.lengthC:=by
    rw [←T.lengths_eq_halfPlane.2.1,←T.lengths_eq_halfPlane.2.2]
    exact circleHalfArcTriangle_equal_sides p R hR hp i hi
  have hbg:=cycle_isosceles_base_angles T.toHalfPlane he
  have hs:=T.toHalfPlane.angle_sum_lt_pi
  rw [←hbg] at hs
  rw [T.angles_eq_halfPlane.2.1]
  exact ⟨T.toHalfPlane.angles_mem_Ioo.2.1.1,by linarith [T.toHalfPlane.angles_mem_Ioo.1.1]⟩

/-- The genuine usable-arc triangle satisfies the source radius identity
with its actual cyclic half-gap and actual measured base angle. -/
theorem circleHalfArcTriangle_identity {n : ℕ} (p : Fin n→Complex.UnitDisc) (R : ℝ)
    (hR : 0<R) (hp : ∀i,‖(p i:ℂ)‖=R) (i : Fin n)
    (hi : circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i∈Ioo (0:ℝ) (Real.pi/2)) :
    Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (p i))*Real.tan (circleHalfArc (fun
      j=>Complex.arg (p j:ℂ)) i)*
      Real.tan (circleHalfArcTriangle p R hR hp i hi).beta=1 := by
  let T:=circleHalfArcTriangle p R hR hp i hi
  have he : T.toHalfPlane.lengthB=T.toHalfPlane.lengthC:=by
    rw [←T.lengths_eq_halfPlane.2.1,←T.lengths_eq_halfPlane.2.2]
    exact circleHalfArcTriangle_equal_sides p R hR hp i hi
  have ht:=cycle_isosceles_half_apex_identity T.toHalfPlane he
  rw [←T.lengths_eq_halfPlane.2.2,←T.angles_eq_halfPlane.1,←T.angles_eq_halfPlane.2.1] at ht
  have hap : T.alpha=2*circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i:=
    circleHalfArcTriangle_apex p R hR hp i hi
  rw [hap,show 2*circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i/2=
    circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i by ring] at ht
  exact ht

/-- The center lies inside the original Dirichlet domain, so every genuine
original vertex has strictly positive actual radius. -/
theorem dirichlet_vertex_radius_positive {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (x : P.domain.carrier) (hx : IsFuchsianPolygonVertex P (dirichletDomain P w) x) :
    0<P.hyperbolicDist w x := by
  have hP:=dirichletDomain_isConvexFuchsianPolygon P w hw
  have hxf:=hx.mem_frontier hP.locallyFinite.fundamental
  apply P.hyperbolicDist_pos.mpr
  intro he
  have hnot : x∉interior (dirichletDomain P w):=hxf.2
  apply hnot
  rw [←he,(dirichletDomain_isOpen P w).interior_eq]
  exact dirichletDomain_center_mem P w hw

end LowDimensionalTopology.Geometry.Fuchsian
