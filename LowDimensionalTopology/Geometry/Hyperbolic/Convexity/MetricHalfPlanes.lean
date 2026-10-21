/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PerpendicularBisectors
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HalfPlanes
@[expose] public section
open Set
open scoped Topology OnePoint UpperHalfPlane Complex.UnitDisc RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

def metricHalfPlaneNormal (a b : ℍ) : ℂ:=
  ⟨((b.im-a.im)-b.im*(a.re^2+a.im^2)+a.im*(b.re^2+b.im^2))/2,
    b.im*a.re-a.im*b.re⟩

def metricHalfPlaneThreshold (a b : ℍ) : ℝ:=
  -((b.im-a.im)+b.im*(a.re^2+a.im^2)-a.im*(b.re^2+b.im^2))/2

/-- The genuine distance comparison becomes an exact affine inequality in the actual Klein coordinate. -/
theorem hyperbolic_metricHalfPlane_affine (a b z : ℍ) :
    dist z a<dist z b ↔ inner ℝ (metricHalfPlaneNormal a b) (halfPlaneKleinCoordinate z)<metricHalfPlaneThreshold a b := by
  have hcosh : Real.cosh (dist z a)<Real.cosh (dist z b) ↔ dist z a<dist z b:=by
    rw [Real.cosh_lt_cosh,abs_of_nonneg dist_nonneg,abs_of_nonneg dist_nonneg]
  rw [←hcosh,UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist']
  rw [div_lt_div_iff₀ (by positivity : 0<2*z.im*a.im) (by positivity : 0<2*z.im*b.im)]
  have hD : 0<z.re^2+z.im^2+1:=by positivity
  have he : inner ℝ (metricHalfPlaneNormal a b) (halfPlaneKleinCoordinate z)-metricHalfPlaneThreshold a b=
      ((b.im-a.im)*(z.re^2+z.im^2)+2*(a.im*b.re-b.im*a.re)*z.re+
        b.im*(a.re^2+a.im^2)-a.im*(b.re^2+b.im^2))/(z.re^2+z.im^2+1):=by
    rw [halfPlaneKleinCoordinate_explicit,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    dsimp [metricHalfPlaneNormal,metricHalfPlaneThreshold]
    field_simp [ne_of_gt hD]
    ring
  let Q:=(b.im-a.im)*(z.re^2+z.im^2)+2*(a.im*b.re-b.im*a.re)*z.re+
    b.im*(a.re^2+a.im^2)-a.im*(b.re^2+b.im^2)
  have hprod : ((z.re-a.re)^2+z.im^2+a.im^2)*(2*z.im*b.im)-
      ((z.re-b.re)^2+z.im^2+b.im^2)*(2*z.im*a.im)=2*z.im*Q:=by dsimp [Q];ring
  conv_lhs=>rw [←sub_lt_zero,hprod]
  conv_rhs=>rw [←sub_lt_zero,he,div_lt_iff₀ hD,zero_mul]
  have hm (q : ℝ) : 2*z.im*q<0 ↔ q<0:=by
    constructor <;> intro h <;> nlinarith [z.im_pos]
  exact hm Q


theorem metricHalfPlaneNormal_swap (a b : ℍ) : metricHalfPlaneNormal b a= -metricHalfPlaneNormal a b := by
  apply Complex.ext <;> dsimp [metricHalfPlaneNormal] <;> ring

theorem metricHalfPlaneThreshold_swap (a b : ℍ) : metricHalfPlaneThreshold b a= -metricHalfPlaneThreshold a b := by
  dsimp [metricHalfPlaneThreshold]
  ring

theorem hyperbolic_metricHalfPlane_affine_le (a b z : ℍ) :
    dist z a≤dist z b ↔ inner ℝ (metricHalfPlaneNormal a b) (halfPlaneKleinCoordinate z)≤metricHalfPlaneThreshold a b := by
  conv_lhs=>rw [←not_lt,hyperbolic_metricHalfPlane_affine b a z,
    metricHalfPlaneNormal_swap,metricHalfPlaneThreshold_swap,inner_neg_left]
  constructor <;> intro h <;> linarith

theorem hyperbolic_metricHalfPlane_affine_eq (a b z : ℍ) :
    dist z a=dist z b ↔ inner ℝ (metricHalfPlaneNormal a b) (halfPlaneKleinCoordinate z)=metricHalfPlaneThreshold a b := by
  have hEq (x y : ℝ) : x=y ↔ x≤y ∧ ¬x<y:=by
    constructor
    · rintro rfl
      exact ⟨le_rfl,lt_irrefl _⟩
    · rintro ⟨hle,hnot⟩
      exact le_antisymm hle (not_lt.mp hnot)
  rw [hEq,hyperbolic_metricHalfPlane_affine_le,hyperbolic_metricHalfPlane_affine,←hEq]

theorem metricHalfPlane_regular {a b : ℍ} (hab : a≠b) :
    metricHalfPlaneNormal a b≠0 ∧ |metricHalfPlaneThreshold a b|<‖metricHalfPlaneNormal a b‖ := by
  have ha : inner ℝ (metricHalfPlaneNormal a b) (halfPlaneKleinCoordinate a)<metricHalfPlaneThreshold a b:=
    (hyperbolic_metricHalfPlane_affine a b a).mp (by simpa only [dist_self] using dist_pos.mpr hab)
  have hb : metricHalfPlaneThreshold a b< inner ℝ (metricHalfPlaneNormal a b) (halfPlaneKleinCoordinate b):=by
    have hh:=(hyperbolic_metricHalfPlane_affine b a b).mp (by simpa only [dist_self] using dist_pos.mpr hab.symm)
    rw [metricHalfPlaneNormal_swap,metricHalfPlaneThreshold_swap,inner_neg_left] at hh
    linarith
  have hn : metricHalfPlaneNormal a b≠0:=by intro he;rw [he,inner_zero_left] at ha hb;linarith
  have hnorm (z : ℍ) : ‖halfPlaneKleinCoordinate z‖<1:=by
    have hz:=mem_range_self z (f:=halfPlaneKleinCoordinate)
    rw [range_halfPlaneKleinCoordinate,Metric.mem_ball,dist_zero_right] at hz
    exact hz
  have hbound (z : ℍ) : |inner ℝ (metricHalfPlaneNormal a b) (halfPlaneKleinCoordinate z)|<‖metricHalfPlaneNormal a b‖:=
    (abs_real_inner_le_norm _ _).trans_lt (by nlinarith [hnorm z,norm_pos_iff.mpr hn])
  refine ⟨hn,abs_lt.mpr ⟨?_,?_⟩⟩
  · have hh:=(abs_lt.mp (hbound a)).1
    exact hh.trans ha
  · exact hb.trans (abs_lt.mp (hbound b)).2

theorem hyperbolic_closer_halfPlane_convex (a b : ℍ) : HConvex {z : ℍ | dist z a<dist z b} := by
  apply (hConvex_iff_cayley_discHConvex _).mpr
  have he : halfPlaneToDisc '' {z : ℍ | dist z a<dist z b}=
      discKleinCutLt (metricHalfPlaneNormal a b) (metricHalfPlaneThreshold a b):=by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (hyperbolic_metricHalfPlane_affine a b w).mp hw
    · intro hz
      refine ⟨discToHalfPlane z,?_,halfPlaneToDisc_discToHalfPlane z⟩
      apply (hyperbolic_metricHalfPlane_affine a b _).mpr
      change inner ℝ (metricHalfPlaneNormal a b) (kleinCoordinate (halfPlaneToDisc (discToHalfPlane z)))<_
      rw [halfPlaneToDisc_discToHalfPlane]
      exact hz
  rw [he]
  exact discKleinCutLt_hConvex _ _


/-- The strict genuine metric side is the actual complementary component of its true bisector geodesic. -/
theorem hyperbolic_closer_halfPlane {a b : ℍ} (hab : a≠b) :
    ∃L : HalfPlaneLine,L.carrier=HEquidistantLocus a b ∧
      {z : ℍ | dist z a<dist z b}=openHHalfPlane L a := by
  obtain ⟨L,hL⟩:=exists_hEquidistantLine hab
  have hcenter : a∈{z : ℍ | dist z a<dist z b}:=by
    change dist a a<dist a b
    simpa only [dist_self] using dist_pos.mpr hab
  have hsub : {z : ℍ | dist z a<dist z b}⊆L.carrierᶜ:=by
    intro z hz hline
    rw [hL] at hline
    exact (ne_of_lt hz) hline
  refine ⟨L,hL,Set.Subset.antisymm ?_ ?_⟩
  · exact (hyperbolic_closer_halfPlane_convex a b).isPreconnected.subset_connectedComponentIn hcenter hsub
  · intro z hz
    by_contra hnot
    let f : ℍ → ℝ:=fun u=>dist u a-dist u b
    have hcont : Continuous f:=(continuous_id.dist continuous_const).sub (continuous_id.dist continuous_const)
    have hfa : f a<0:=by dsimp [f];rw [dist_self,zero_sub];exact neg_neg_of_pos (dist_pos.mpr hab)
    have hfz : 0≤f z:=sub_nonneg.mpr (not_lt.mp hnot)
    have hpre:=(isPreconnected_connectedComponentIn (F:=L.carrierᶜ) (x:=a)).image f hcont.continuousOn
    have hA:=mem_image_of_mem f (mem_connectedComponentIn (hsub hcenter))
    have hZ:=mem_image_of_mem f hz
    have hzero : (0 : ℝ)∈f '' connectedComponentIn L.carrierᶜ a:=hpre.ordConnected.out hA hZ ⟨hfa.le,hfz⟩
    obtain ⟨u,hu,hue⟩:=hzero
    have he : dist u a=dist u b:=sub_eq_zero.mp hue
    apply connectedComponentIn_subset L.carrierᶜ a hu
    rw [hL]
    exact he

end
end LowDimensionalTopology.Geometry.Hyperbolic
