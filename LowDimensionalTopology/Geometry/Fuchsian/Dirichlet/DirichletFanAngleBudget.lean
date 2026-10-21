/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletFanTriangles
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.ProperSectorAngularMeasure
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.PlaneSeparation
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped Complex.UnitDisc ENNReal BigOperators
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- Genuine subtended angular measure is monotone in its original point set. -/
theorem cycle_subtendedAngle_mono {S T : Set Complex.UnitDisc} (h : S⊆T) (z : Complex.UnitDisc) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle S z≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle T z := by
  unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_mono (Set.image_mono h)))

/-- The actual angles of finitely many disjoint convex open fan regions
through a common basepoint fit within the containing original point set.
The angular budget is proved from the actual disjointness and inclusion. -/
theorem cycle_fan_angle_sum_le {ι : Type*} [Fintype ι]
    (U : ι→Set Complex.UnitDisc) (S : Set Complex.UnitDisc)
    (hc : ∀i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (U i)) (ho : ∀i,IsOpen (U i)) (hn : ∀i,(U
      i).Nonempty)
    (h0 : ∀i,(0:Complex.UnitDisc)∈closure (U i))
    (hd : Pairwise (fun i j=>Disjoint (U i) (U j))) (hsub : ∀i,closure (U i)⊆S) :
    ∑i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure (U i)) 0≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle S 0 := by
  classical
  have hm:=measure_biUnion_finset₀ (μ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure)
    (s:=(Finset.univ:Finset ι)) (f:=fun i=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections
      (closure (U i)))
    (fun i _ j _ hij=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.finite_discRadialDirections_common_closures
      (hc i) (ho i) (hn i) (hc j) (ho j) (hn j) (hd hij) (h0 i) (h0 j)).measure_zero _)
    (fun i _=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.measurableSet_discRadialDirections (hc i).closure
      isClosed_closure (h0 i)).nullMeasurableSet)
  simp only [Finset.mem_univ,iUnion_true] at hm
  have hmeasure : (∑i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (closure (U i))))≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections S):=by
    rw [←hm]
    apply measure_mono
    apply iUnion_subset
    intro i
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_mono (hsub i)
  have hr:=ENNReal.toReal_mono (measure_ne_top _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure
    _) hmeasure
  rw [ENNReal.toReal_sum (fun i _=>measure_ne_top
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure _)] at hr
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction_zero,←Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hr (by positivity)

/-- A genuine affine sign at a native triangle's actual vertices gives
its strict sign at every actual interior point. -/
theorem cycle_triangle_inner_positive (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscTriangle) (ha : T.a=0)
    (n : ℂ) (hb : 0≤ inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate T.b))
    (hc : 0≤ inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate T.c))
    (hpos : 0< inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate T.b) ∨ 0< inner ℝ n
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate T.c))
    (z : Complex.UnitDisc) (hz : z∈T.interior) : 0< inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) := by
  have hzh : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z∈T.toHalfPlane.interior:=by
    have h:=hz
    rw [T.interior_eq_cayley] at h
    obtain ⟨u,hu,he⟩:=h
    rw [←he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
    exact hu
  have hcoord:=mem_image_of_mem T.toHalfPlane.coordinate hzh
  rw [T.toHalfPlane.coordinate_image_interior] at hcoord
  have h1 : 0<(T.toHalfPlane.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
    z)).1:=hcoord.1
  have h2 : 0<(T.toHalfPlane.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
    z)).2:=hcoord.2.1
  have hr:=T.toHalfPlane.inner_klein_reconstruction n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
    z)
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscTriangle.toHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane] at hr
  have hzero : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (0:Complex.UnitDisc)=0:=by
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]
  have hzeroA : inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate T.a)=0:=by rw [ha,hzero,inner_zero_right]
  rw [hzeroA,sub_zero,sub_zero,zero_add] at hr
  rw [hr]
  rcases hpos with hp|hp
  · exact add_pos_of_pos_of_nonneg (mul_pos h1 hp) (mul_nonneg h2.le hc)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg h1.le hb) (mul_pos h2 hp)

/-- Two original triangles on opposite sides of their actual shared radial
line have disjoint genuine interiors. -/
theorem cycle_triangles_opposite_disjoint (T U : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscTriangle) (ha :
  T.a=0) (hua : U.a=0)
    (n : ℂ) (hTb : 0≤ inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate T.b))
    (hTc : 0≤ inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate T.c))
    (hTp : 0< inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate T.b) ∨ 0< inner ℝ n
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate T.c))
    (hUb : inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate U.b)≤0)
    (hUc : inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate U.c)≤0)
    (hUp : inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate U.b)<0 ∨ inner ℝ n
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate U.c)<0) :
    Disjoint T.interior U.interior := by
  apply Set.disjoint_left.mpr
  intro z hzT hzU
  have ht:=cycle_triangle_inner_positive T ha n hTb hTc hTp z hzT
  have hu:=cycle_triangle_inner_positive U hua (-n) (by simpa only [inner_neg_left] using neg_nonneg.mpr hUb)
    (by simpa only [inner_neg_left] using neg_nonneg.mpr hUc) (by
      simpa only [inner_neg_left,neg_pos] using hUp) z hzU
  rw [inner_neg_left] at hu
  linarith

/-- The proved finite geometric fan budget holds at every original native
basepoint, using a constructed genuine isometry to zero. -/
theorem cycle_fan_angle_sum_le_at {ι : Type*} [Fintype ι]
    (U : ι→Set Complex.UnitDisc) (S : Set Complex.UnitDisc) (z : Complex.UnitDisc)
    (hc : ∀i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (U i)) (ho : ∀i,IsOpen (U i)) (hn : ∀i,(U
      i).Nonempty)
    (hz : ∀i,z∈closure (U i))
    (hd : Pairwise (fun i j=>Disjoint (U i) (U j))) (hsub : ∀i,closure (U i)⊆S) :
    ∑i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure (U i)) z≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle S z := by
  classical
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer z
  have hF:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry z
  have hFz : F z=0:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self z
  have hzero (i : ι) : (0:Complex.UnitDisc)∈closure (F '' U i):=by
    rw [←F.image_closure,←hFz]
    exact mem_image_of_mem F (hz i)
  have hle:=cycle_fan_angle_sum_le (fun i=>F '' U i) (F '' S)
    (fun i=>(hc i).isometry_image hF) (fun i=>F.isOpenMap _ (ho i))
    (fun i=>(hn i).image F) hzero
    (fun i j hij=>(hd hij).image F.injective.injOn (subset_univ _) (subset_univ _))
    (fun i=>by rw [←F.image_closure];exact image_mono (hsub i))
  have he (i : ι) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure (F '' U i)) 0=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure (U i)) z:=by
    rw [←F.image_closure,←hFz]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle_isometry F hF _ z
  calc
    (∑i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure (U i))
      z)=∑i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure (F '' U i)) 0:=
      Finset.sum_congr rfl (fun i _=>(he i).symm)
    _≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (F '' S) 0:=hle
    _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle S z:=by
      rw [←hFz]
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle_isometry F hF S z

/-- The true radial Klein line has its original oriented Euclidean determinant. -/
theorem cycle_radial_normal_inner (x y : Complex.UnitDisc) :
    inner ℝ (Complex.I*(x:ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate y)=
      (2/(1+‖(y:ℂ)‖^2))*((x:ℂ).re*(y:ℂ).im-(x:ℂ).im*(y:ℂ).re) := by
  change inner ℝ (Complex.I*(x:ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (y:ℂ))=_
  rw [real_inner_comm,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula_inner,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add,zero_sub]
  ring

/-- The two genuine adjacent usable fan triangles lie on opposite sides of
their true common radial geodesic, hence have disjoint actual interiors. -/
theorem adjacent_circle_fan_disjoint {n : ℕ} (p : Fin n→Complex.UnitDisc) (R : ℝ)
    (hR : 0<R) (hp : ∀i,‖(p i:ℂ)‖=R) (i : Fin n)
    (hi : circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i∈Ioo (0:ℝ) (Real.pi/2))
    (hj : circleHalfArc (fun j=>Complex.arg (p j:ℂ)) ((finRotate n).symm i)∈Ioo (0:ℝ) (Real.pi/2)) :
    Disjoint (circleHalfArcTriangle p R hR hp i hi).interior
      (circleHalfArcTriangle p R hR hp ((finRotate n).symm i) hj).interior := by
  let j:=(finRotate n).symm i
  have hnext : finRotate n j=i:=(finRotate n).apply_symm_apply i
  have hdet : 0<(p i:ℂ).re*(p (finRotate n i):ℂ).im-(p i:ℂ).im*(p (finRotate n i):ℂ).re:=by
    rw [circleHalfArc_determinant p R hp i]
    exact mul_pos (sq_pos_of_pos hR) (Real.sin_pos_of_pos_of_lt_pi
      (by linarith only [hi.1]) (by linarith only [hi.2]))
  have hdetj : 0<(p j:ℂ).re*(p i:ℂ).im-(p j:ℂ).im*(p i:ℂ).re:=by
    have ht:=circleHalfArc_determinant p R hp j
    rw [hnext] at ht
    rw [ht]
    exact mul_pos (sq_pos_of_pos hR) (Real.sin_pos_of_pos_of_lt_pi
      (by linarith only [hj.1]) (by linarith only [hj.2]))
  let N:=Complex.I*(p i:ℂ)
  have hself : inner ℝ N (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (p i))=0:=by
    rw [cycle_radial_normal_inner]
    ring
  have hright : 0 < inner ℝ N (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (p (finRotate n i))):=by
    rw [cycle_radial_normal_inner]
    exact mul_pos (by positivity) hdet
  have hleft : inner ℝ N (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (p j))<0:=by
    rw [cycle_radial_normal_inner]
    exact mul_neg_of_pos_of_neg (by positivity) (by linarith only [hdetj])
  apply cycle_triangles_opposite_disjoint _ _ rfl rfl N
  · exact hself.ge
  · exact hright.le
  · exact Or.inr hright
  · exact hleft.le
  · change inner ℝ N (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (p (finRotate n j)))≤0
    rw [hnext]
    exact hself.le
  · exact Or.inl hleft

/-- The sum of the two independently measured true triangle angles at a
shared finite corner is bounded by their actual containing original sector. -/
theorem cycle_two_triangle_angles_le (T U : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (S :
  Set Complex.UnitDisc)
    (z : Complex.UnitDisc) (hT : T.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (hU :
      U.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hd : Disjoint T.interior U.interior) (hTS : T.finiteCarrier⊆S) (hUS : U.finiteCarrier⊆S) :
    T.alpha+U.alpha≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle S z := by
  classical
  let V : Fin 2→Set Complex.UnitDisc:=![T.interior,U.interior]
  have hc : ∀i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (V i):=by intro i;fin_cases i;exact T.interior_discHConvex;exact U.interior_discHConvex
  have ho : ∀i,IsOpen (V i):=by intro i;fin_cases i;exact T.interior_isOpen;exact U.interior_isOpen
  have hn : ∀i,(V i).Nonempty:=by intro i;fin_cases i;exact T.interior_nonempty;exact U.interior_nonempty
  have h0T : z∈T.finiteCarrier:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvexHull {T.a,T.b,T.c}
    rw [←hT]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.subset_closedDiscHConvexHull _ (by simp)
  have h0U : z∈U.finiteCarrier:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvexHull {U.a,U.b,U.c}
    rw [←hU]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.subset_closedDiscHConvexHull _ (by simp)
  have hz : ∀i,z∈closure (V i):=by
    intro i;fin_cases i
    · exact T.finiteCarrier_eq_closure ▸ h0T
    · exact U.finiteCarrier_eq_closure ▸ h0U
  have hdV : Pairwise (fun i j=>Disjoint (V i) (V j)):=by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hij rfl).elim
  have hs : ∀i,closure (V i)⊆S:=by
    intro i;fin_cases i
    · exact T.finiteCarrier_eq_closure ▸ hTS
    · exact U.finiteCarrier_eq_closure ▸ hUS
  have hh:=cycle_fan_angle_sum_le_at V S z hc ho hn hz hdV hs
  have hAT:=T.subtendedAngle_at_finite z hT
  have hAU:=U.subtendedAngle_at_finite z hU
  rw [T.finiteCarrier_eq_closure] at hAT
  rw [U.finiteCarrier_eq_closure] at hAU
  simpa only [Fin.sum_univ_two,V,Matrix.cons_val_zero,Matrix.cons_val_one,hAT,hAU] using hh

/-- A genuine finite triangle corner is bounded by its actual containing sector. -/
theorem cycle_triangle_angle_le (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (S : Set
  Complex.UnitDisc)
    (z : Complex.UnitDisc) (hT : T.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (hTS :
      T.finiteCarrier⊆S) :
    T.alpha≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle S z := by
  rw [←T.subtendedAngle_at_finite z hT]
  exact cycle_subtendedAngle_mono hTS z

/-- The two actual neighboring usable fan base angles fit within the genuine
containing convex region at their original common circle point. -/
theorem adjacent_circle_fan_angle_le {n : ℕ} (p : Fin n→Complex.UnitDisc) (R : ℝ)
    (hR : 0<R) (hp : ∀i,‖(p i:ℂ)‖=R) (i : Fin n)
    (hi : circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i∈Ioo (0:ℝ) (Real.pi/2))
    (hj : circleHalfArc (fun j=>Complex.arg (p j:ℂ)) ((finRotate n).symm i)∈Ioo (0:ℝ) (Real.pi/2))
    (S : Set Complex.UnitDisc) (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S) (h0S :
      (0:Complex.UnitDisc)∈S)
    (hps : ∀i,p i∈S) :
    (circleHalfArcTriangle p R hR hp i hi).beta+
      (circleHalfArcTriangle p R hR hp ((finRotate n).symm i) hj).beta≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle S (p i) := by
  let j:=(finRotate n).symm i
  have hnext : finRotate n j=i:=(finRotate n).apply_symm_apply i
  let T:=circleHalfArcTriangle p R hR hp i hi
  let U:=circleHalfArcTriangle p R hR hp j hj
  have hTcl : closure T.interior⊆S:=T.closure_min_discHConvex hS h0S (hps i) (hps _)
  have hUcl : closure U.interior⊆S:=U.closure_min_discHConvex hS h0S (hps j) (hps _)
  have hd : Disjoint T.toClosedDiscTriangle.cycle.interior U.toClosedDiscTriangle.cycle.cycle.interior:=by
    rw [T.toClosedDiscTriangle.cycle_interior,U.toClosedDiscTriangle.cycle.cycle_interior,
      U.toClosedDiscTriangle.cycle_interior,T.interior_toClosedDiscTriangle,U.interior_toClosedDiscTriangle]
    exact adjacent_circle_fan_disjoint p R hR hp i hi hj
  have hTc : T.toClosedDiscTriangle.cycle.finiteCarrier⊆S:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.finiteCarrier_eq_closure,T.toClosedDiscTriangle.cycle_interior,
      T.interior_toClosedDiscTriangle]
    exact hTcl
  have hUc : U.toClosedDiscTriangle.cycle.cycle.finiteCarrier⊆S:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.finiteCarrier_eq_closure,U.toClosedDiscTriangle.cycle.cycle_interior,
      U.toClosedDiscTriangle.cycle_interior,U.interior_toClosedDiscTriangle]
    exact hUcl
  have hUA : U.toClosedDiscTriangle.cycle.cycle.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (p i):=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (p (finRotate n
      j))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (p i)
    rw [hnext]
  have hh:=cycle_two_triangle_angles_le T.toClosedDiscTriangle.cycle
    U.toClosedDiscTriangle.cycle.cycle S (p i) rfl hUA hd hTc hUc
  have heU : U.toHalfPlane.lengthB=U.toHalfPlane.lengthC:=by
    rw [←U.lengths_eq_halfPlane.2.1,←U.lengths_eq_halfPlane.2.2]
    exact circleHalfArcTriangle_equal_sides p R hR hp j hj
  have hbg:=cycle_isosceles_base_angles U.toHalfPlane heU
  rw [←U.angles_eq_halfPlane.2.1,←U.angles_eq_halfPlane.2.2] at hbg
  change T.toClosedDiscTriangle.beta+U.toClosedDiscTriangle.gamma≤_ at hh
  rw [T.closed_angles.2.1,U.closed_angles.2.2,←hbg] at hh
  exact hh

/-- The actual common isosceles base angle is bounded at both genuine
endpoints by the containing original convex region. -/
theorem circle_fan_base_angle_bounds {n : ℕ} (p : Fin n→Complex.UnitDisc) (R : ℝ)
    (hR : 0<R) (hp : ∀i,‖(p i:ℂ)‖=R) (i : Fin n)
    (hi : circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i∈Ioo (0:ℝ) (Real.pi/2))
    (S : Set Complex.UnitDisc) (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S) (h0S :
      (0:Complex.UnitDisc)∈S)
    (hps : ∀i,p i∈S) :
    (circleHalfArcTriangle p R hR hp i
      hi).beta≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle S (p i) ∧
    (circleHalfArcTriangle p R hR hp i hi).beta≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle S (p (finRotate n i)) := by
  let T:=circleHalfArcTriangle p R hR hp i hi
  have hcl : closure T.interior⊆S:=T.closure_min_discHConvex hS h0S (hps i) (hps _)
  have hC : T.toClosedDiscTriangle.cycle.finiteCarrier⊆S:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.finiteCarrier_eq_closure,T.toClosedDiscTriangle.cycle_interior,
      T.interior_toClosedDiscTriangle]
    exact hcl
  have hCC : T.toClosedDiscTriangle.cycle.cycle.finiteCarrier⊆S:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.finiteCarrier_eq_closure,T.toClosedDiscTriangle.cycle.cycle_interior,
      T.toClosedDiscTriangle.cycle_interior,T.interior_toClosedDiscTriangle]
    exact hcl
  have hleft:=cycle_triangle_angle_le T.toClosedDiscTriangle.cycle S (p i) rfl hC
  have hright:=cycle_triangle_angle_le T.toClosedDiscTriangle.cycle.cycle S (p (finRotate n i)) rfl hCC
  change T.toClosedDiscTriangle.beta≤_ at hleft
  change T.toClosedDiscTriangle.gamma≤_ at hright
  rw [T.closed_angles.2.1] at hleft
  rw [T.closed_angles.2.2] at hright
  have he : T.toHalfPlane.lengthB=T.toHalfPlane.lengthC:=by
    rw [←T.lengths_eq_halfPlane.2.1,←T.lengths_eq_halfPlane.2.2]
    exact circleHalfArcTriangle_equal_sides p R hR hp i hi
  have hbg:=cycle_isosceles_base_angles T.toHalfPlane he
  rw [←T.angles_eq_halfPlane.2.1,←T.angles_eq_halfPlane.2.2] at hbg
  exact ⟨hleft,hbg ▸ hright⟩

/-- The actual measured base angle on each usable arc; a missing nonminor
fan contributes zero rather than any supplied angle data. -/
def circleFanBaseAngle {n : ℕ} (p : Fin n→Complex.UnitDisc) (R : ℝ)
    (hR : 0<R) (hp : ∀i,‖(p i:ℂ)‖=R) (i : Fin n) : ℝ:=
  if hi : circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i∈Ioo (0:ℝ) (Real.pi/2) then
    (circleHalfArcTriangle p R hR hp i hi).beta else 0

/-- The two actual adjacent contributions satisfy the original region's
pointwise angle budget, including both one-missing-arc cases. -/
theorem circleFanBaseAngle_adjacent_le {n : ℕ} (p : Fin n→Complex.UnitDisc) (R : ℝ)
    (hR : 0<R) (hp : ∀i,‖(p i:ℂ)‖=R) (i : Fin n)
    (S : Set Complex.UnitDisc) (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S) (h0S :
      (0:Complex.UnitDisc)∈S)
    (hps : ∀i,p i∈S) :
    circleFanBaseAngle p R hR hp i+circleFanBaseAngle p R hR hp ((finRotate n).symm i)≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle S (p i) := by
  by_cases hi : circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i∈Ioo (0:ℝ) (Real.pi/2)
  · by_cases hj : circleHalfArc (fun j=>Complex.arg (p j:ℂ)) ((finRotate n).symm i)∈Ioo (0:ℝ) (Real.pi/2)
    · simpa only [circleFanBaseAngle,dite_eq_left hi,dite_eq_left hj] using
        adjacent_circle_fan_angle_le p R hR hp i hi hj S hS h0S hps
    · simpa only [circleFanBaseAngle,dite_eq_left hi,dite_eq_right hj,add_zero] using
        (circle_fan_base_angle_bounds p R hR hp i hi S hS h0S hps).1
  · by_cases hj : circleHalfArc (fun j=>Complex.arg (p j:ℂ)) ((finRotate n).symm i)∈Ioo (0:ℝ) (Real.pi/2)
    · have hh:=(circle_fan_base_angle_bounds p R hR hp ((finRotate n).symm i) hj S hS h0S hps).2
      rw [(finRotate n).apply_symm_apply] at hh
      simpa only [circleFanBaseAngle,dite_eq_right hi,dite_eq_left hj,zero_add] using hh
    · simp only [circleFanBaseAngle,dite_eq_right hi,dite_eq_right
      hj,zero_add,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle]
      positivity

/-- The finite usable fan's true base-angle sum is bounded by half the sum
of the actual original containing region's corner angles. -/
theorem circleFanBaseAngle_sum_le {n : ℕ} (p : Fin n→Complex.UnitDisc) (R : ℝ)
    (hR : 0<R) (hp : ∀i,‖(p i:ℂ)‖=R)
    (S : Set Complex.UnitDisc) (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S) (h0S :
      (0:Complex.UnitDisc)∈S)
    (hps : ∀i,p i∈S) :
    2*(∑i,circleFanBaseAngle p R hR hp i)≤∑i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle S (p i) := by
  have hh:=Finset.sum_le_sum (fun i (_hi : i∈(Finset.univ:Finset (Fin n)))=>
    circleFanBaseAngle_adjacent_le p R hR hp i S hS h0S hps)
  rw [Finset.sum_add_distrib] at hh
  have he : ∑i,circleFanBaseAngle p R hR hp ((finRotate n).symm i)=
      ∑i,circleFanBaseAngle p R hR hp i:=Equiv.sum_comp (finRotate n).symm _
  rw [he] at hh
  linarith only [hh]

open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Polygon

/-- The literal original closed Dirichlet domain in its constructed genuine
native disc coordinate sending the original center to zero. -/
def dirichletNormalizedClosure {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) : Set Complex.UnitDisc:=
  cycleOriginCoordinate P w '' closure (dirichletDomain P w)

theorem dirichletNormalizedClosure_convex {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (dirichletNormalizedClosure P w) := by
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate w)
  have hp:=dirichletDomain_isConvexFuchsianPolygon P w hw
  have hh:=hp.convex.closure.isometry_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry (P.finiteCoordinate w))
  have he : dirichletNormalizedClosure P w=F '' closure (P.finiteCoordinate '' dirichletDomain P w):=by
    rw [←P.finiteCoordinate.image_closure,Set.image_image]
    rfl
  rw [he]
  exact hh

theorem dirichletNormalizedClosure_zero {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) :
    (0:Complex.UnitDisc)∈dirichletNormalizedClosure P w := by
  have hz : cycleOriginCoordinate P w w=0:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self (P.finiteCoordinate w)
  rw [←hz]
  exact mem_image_of_mem _ (subset_closure (dirichletDomain_center_mem P w hw))

/-- The actual normalized containing-sector angle is exactly the original
independently defined Dirichlet polygon angle. -/
theorem dirichletNormalizedClosure_angle {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w x : P.domain.carrier) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (dirichletNormalizedClosure P
      w) (cycleOriginCoordinate P w x)=
      fuchsianPolygonAngle P (dirichletDomain P w) x := by
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate w)
  have he : dirichletNormalizedClosure P w=F '' (P.finiteCoordinate '' closure (dirichletDomain P w)):=by
    rw [Set.image_image]
    rfl
  rw [he]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (F '' (P.finiteCoordinate '' closure
    (dirichletDomain P w)))
    (F (P.finiteCoordinate x))=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle_isometry F
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry (P.finiteCoordinate w))]
  rfl

/-- All actual finite fan data and its true base-angle budget are derived
from the original accidental Dirichlet vertex cycle and its original action. -/
theorem dirichlet_cycle_actual_fan_data {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (x : P.domain.carrier) (hx : IsFuchsianPolygonVertex P (dirichletDomain P w) x)
    (ha : IsAccidentalFuchsianPoint P x) :
    ∃(n : ℕ) (α θ : Fin n→ℝ),
      n=fuchsianPolygonCycleLength P (fuchsianPolygonCycle P (dirichletDomain P w) x) ∧
      (∀i,0<α i) ∧ (∑i,α i)=Real.pi ∧
      (∑i∈Finset.univ.filter (fun i=>α i<Real.pi/2),θ i)≤Real.pi ∧
      ∀i,α i<Real.pi/2 → θ i∈Ioo (0:ℝ) (Real.pi/2) ∧
        Real.cosh (P.hyperbolicDist w x)*Real.tan (α i)*Real.tan (θ i)=1 := by
  classical
  obtain ⟨s,hs,e,he⟩:=dirichlet_cycle_argument_order P w hw x hx
  have hP:=dirichletDomain_isConvexFuchsianPolygon P w hw
  have hxc : x∈fuchsianPolygonCycle P (dirichletDomain P w) x:=
    ⟨(hx.mem_frontier hP.locallyFinite.fundamental).1,⟨1,one_smul _ _⟩⟩
  have hpm (i : Fin s.card) : (e i).val∈fuchsianPolygonCycle P (dirichletDomain P w) x:=by
    rw [←hs]
    exact (e i).property
  let p : Fin s.card→Complex.UnitDisc:=fun i=>cycleOriginCoordinate P w (e i).val
  let r:=P.hyperbolicDist w x
  let R:=Real.tanh (r/2)
  have hr : 0<r:=dirichlet_vertex_radius_positive P w hw x hx
  have hR : 0<R:=by
    change 0<Real.tanh (r/2)
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith only [hr])) (Real.cosh_pos _)
  have hp : ∀i,‖(p i:ℂ)‖=R:=by
    intro i
    apply cycleOriginCoordinate_norm P w (e i).val r
    change P.hyperbolicDist w (e i).val=P.hyperbolicDist w x
    rw [P.hyperbolicDist_comm w (e i).val,P.hyperbolicDist_comm w x]
    exact dirichlet_cycle_distance_to_center_eq P w x (hpm i) hxc
  let α : Fin s.card→ℝ:=circleHalfArc (fun i=>Complex.arg (p i:ℂ))
  let θ : Fin s.card→ℝ:=circleFanBaseAngle p R hR hp
  have hα : ∀i,0<α i:=fun i=>circleHalfArc_positive _ he (fun j=>Complex.arg_mem_Ioc _) i
  have hcard : s.card=fuchsianPolygonCycleLength P (fuchsianPolygonCycle P (dirichletDomain P w) x):=by
    unfold fuchsianPolygonCycleLength
    rw [←hs,Set.ncard_coe_finset]
  have hn : 3≤s.card:=by
    rw [hcard]
    exact hP.accidental_vertex_cycle_length_ge_three x hx ha
  let S:=dirichletNormalizedClosure P w
  have hps : ∀i,p i∈S:=fun i=>mem_image_of_mem _ (hpm i).1
  have hsum:=circleFanBaseAngle_sum_le p R hR hp S
    (dirichletNormalizedClosure_convex P w hw) (dirichletNormalizedClosure_zero P w hw) hps
  have hsf : s=(hP.locallyFinite.cycle_finite x).toFinset:=
    Finset.coe_injective (hs.trans (hP.locallyFinite.cycle_finite x).coe_toFinset.symm)
  have hOrder : fuchsianPointOrder P x=1:=
    (isAccidentalFuchsianPoint_iff_pointOrder_one P x).mp ha
  have hAngles : (∑y∈s,fuchsianPolygonAngle P (dirichletDomain P w) y)=2*Real.pi:=by
    have hh:=sum_cycle_angles_eq_two_pi_div_pointOrder hP x
    simpa only [←hsf,hOrder,Nat.cast_one,div_one] using hh
  have hactualAngles : (∑i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle S (p i))=2*Real.pi:=by
    calc
      (∑i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle S (p i))=
          ∑i,fuchsianPolygonAngle P (dirichletDomain P w) (e i).val:=by
        apply Finset.sum_congr rfl
        intro i _
        exact dirichletNormalizedClosure_angle P w (e i).val
      _=∑y:s,fuchsianPolygonAngle P (dirichletDomain P w) y.val:=Equiv.sum_comp e (fun y:s=>fuchsianPolygonAngle P
        (dirichletDomain P w) y.val)
      _=∑y∈s,fuchsianPolygonAngle P (dirichletDomain P w) y:=Finset.sum_coe_sort _ _
      _=2*Real.pi:=hAngles
  rw [hactualAngles] at hsum
  have hθsum : (∑i,θ i)≤Real.pi:=by linarith only [hsum]
  have hθnn : ∀i,0≤θ i:=by
    intro i
    dsimp only [θ,circleFanBaseAngle]
    split_ifs with hi
    · exact (circleHalfArcTriangle_base_acute p R hR hp i hi).1.le
    · exact le_rfl
  have hfilter : (∑i∈Finset.univ.filter (fun i=>α i<Real.pi/2),θ i)≤Real.pi:=by
    apply le_trans _ hθsum
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _=>hθnn i)
  refine ⟨s.card,α,θ,hcard,hα,circleHalfArc_sum (by omega) _,hfilter,?_⟩
  intro i hi
  have hu : circleHalfArc (fun j=>Complex.arg (p j:ℂ)) i∈Ioo (0:ℝ) (Real.pi/2):=⟨hα i,hi⟩
  have hθ : θ i=(circleHalfArcTriangle p R hR hp i hu).beta:=by
    simp only [θ,circleFanBaseAngle,dite_eq_left hu]
  refine ⟨hθ.symm ▸ circleHalfArcTriangle_base_acute p R hR hp i hu,?_⟩
  have hid:=circleHalfArcTriangle_identity p R hR hp i hu
  have hri : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (p
    i)=r:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_distance_zero_eq_iff (p i) r).mpr (hp i)
  rw [hri,←hθ] at hid
  exact hid

/-- The exact numerical step uses the identity already proved for the
actual isosceles fan, without postulating a right-triangle object. -/
theorem cycle_cosh_radius_of_tan_identity (r a b : ℝ)
    (hα : a∈Ioo (0:ℝ) (Real.pi/2)) (hβ : b∈Ioo (0:ℝ) (Real.pi/2))
    (n : ℕ) (hn : 5≤n) (hangle : a+b≤2*Real.pi/(n:ℝ))
    (hidentity : Real.cosh r*Real.tan a*Real.tan b=1) :
    Real.cot (Real.pi/(n:ℝ))^2≤Real.cosh r := by
  have hnR : (5:ℝ)≤n:=by exact_mod_cast hn
  have hn0 : (0:ℝ)<n:=by linarith only [hnR]
  have hsmall : 2*Real.pi/(n:ℝ)<Real.pi/2:=by
    apply (div_lt_iff₀ hn0).mpr
    nlinarith only [mul_pos (show 0<(n:ℝ)-4 by linarith only [hnR]) Real.pi_pos]
  have hsum : a+b<Real.pi/2:=hangle.trans_lt hsmall
  have hp:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.tangent_product hα hβ hsum
  have hBpos : 0<Real.pi/(n:ℝ):=div_pos Real.pi_pos hn0
  have hBlt : Real.pi/(n:ℝ)<Real.pi/2:=by
    apply (div_lt_iff₀ hn0).mpr
    nlinarith only [mul_pos (show 0<(n:ℝ)-2 by linarith only [hnR]) Real.pi_pos]
  have hhalf : (a+b)/2≤Real.pi/(n:ℝ):=by
    have he : a+b≤2*(Real.pi/(n:ℝ)):=by simpa only [mul_div_assoc] using hangle
    linarith only [he]
  have ht:=Real.strictMonoOn_tan.monotoneOn
    (show (a+b)/2∈Ioo (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [hα.1,hβ.1,Real.pi_pos],by linarith only [hsum,Real.pi_pos]⟩)
    (show Real.pi/(n:ℝ)∈Ioo (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [hBpos,Real.pi_pos],hBlt⟩) hhalf
  have ht0 : 0≤Real.tan ((a+b)/2):=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith [hα.1,hβ.1]) (by linarith only [hsum,Real.pi_pos])
  have hprod : Real.tan a*Real.tan b≤Real.tan (Real.pi/(n:ℝ))^2:=
    hp.trans ((sq_le_sq₀ ht0 (ht0.trans ht)).mpr ht)
  have hid:=hidentity
  have hmul:=mul_le_mul_of_nonneg_left hprod (Real.cosh_pos r).le
  have htan : 0<Real.tan (Real.pi/(n:ℝ)):=Real.tan_pos_of_pos_of_lt_pi_div_two hBpos hBlt
  rw [←Real.tan_inv_eq_cot,inv_pow]
  apply (inv_le_iff_one_le_mul₀ (sq_pos_of_pos htan)).mpr
  nlinarith only [hid,hmul]
/--
For the actual original Dirichlet polygon, its
literal accidental cycle and genuine metric radius. All fan data and the
base-angle budget are constructed from the original source hypotheses.
-/
theorem cot_cycle_angle_sq_le_cosh_dirichlet_vertex_distance {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (x : P.domain.carrier) (hx : IsFuchsianPolygonVertex P (dirichletDomain P w) x)
    (ha : IsAccidentalFuchsianPoint P x)
    (hn : 5≤fuchsianPolygonCycleLength P (fuchsianPolygonCycle P (dirichletDomain P w) x)) :
    Real.cot (Real.pi/(fuchsianPolygonCycleLength P (fuchsianPolygonCycle P (dirichletDomain P w) x):ℝ))^2≤
      Real.cosh (P.hyperbolicDist w x) := by
  obtain ⟨n,α,θ,hcard,hα,hsum,hbudget,hT⟩:=dirichlet_cycle_actual_fan_data P w hw x hx ha
  have hn5 : 5≤n:=hcard.symm ▸ hn
  obtain ⟨i,hi,hsmall⟩:=cyclic_half_arc_small_pair hn5 α θ hα hsum hbudget
  obtain ⟨hθ,hid⟩:=hT i hi
  rw [←hcard]
  exact cycle_cosh_radius_of_tan_identity (P.hyperbolicDist w x) (α i) (θ i)
    ⟨hα i,hi⟩ hθ n hn5 hsmall hid

/-- A rigorous rational version of the source's displayed decimal bound,
for every original accidental cycle of length at least five. -/
theorem oneHundredEightyNine_div_hundred_lt_cosh_dirichlet_vertex_distance {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (x : P.domain.carrier) (hx : IsFuchsianPolygonVertex P (dirichletDomain P w) x)
    (ha : IsAccidentalFuchsianPoint P x)
    (hn : 5≤fuchsianPolygonCycleLength P (fuchsianPolygonCycle P (dirichletDomain P w) x)) :
    (189:ℝ)/100<Real.cosh (P.hyperbolicDist w x) :=
  (cot_sq_pi_div_nat_gt_189_div_100 _ hn).trans_le (cot_cycle_angle_sq_le_cosh_dirichlet_vertex_distance P w hw x hx ha
    hn)

end LowDimensionalTopology.Geometry.Fuchsian
