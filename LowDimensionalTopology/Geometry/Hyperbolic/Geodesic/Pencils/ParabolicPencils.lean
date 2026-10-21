/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.PencilRatioClassification
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.GeodesicReflections
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PerpendicularBisectors

/-!
# Genuine parabolic pencils and complementary horocycles
-/
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Inversive
noncomputable section

def horizontalHorocycle (t : ℝ) : Set ℍ := {z | z.im=t}

def horizontalHorocycleCircle (t : ℝ) : Mobius.ComplexGeneralizedCircle :=
  ⟨Mobius.complexLine Complex.I t,Mobius.complexLine_isGeneralized Complex.I t Complex.I_ne_zero⟩

theorem horizontalHorocycle_eq_actual_boundary (t : ℝ) :
    horizontalHorocycle t=hHorocycle (horizontalHorocyclicRegion t) := by
  change horizontalHorocycle t=frontier (UpperHalfPlane.im ⁻¹' Ioi t)
  rw [←UpperHalfPlane.isOpenMap_im.preimage_frontier_eq_frontier_preimage UpperHalfPlane.continuous_im,
    frontier_Ioi]
  rfl

theorem horizontalHorocycle_eq_circleCarrier (t : ℝ) (z : ℍ) :
    z∈horizontalHorocycle t ↔ ((z : ℂ) : OnePoint ℂ)∈(horizontalHorocycleCircle t).val := by
  change z.im=t ↔ ((z : ℂ) : OnePoint ℂ)∈Mobius.complexLine Complex.I t
  rw [Mobius.complexLine_coe,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
  simp

def parabolicPencilAtInfinity : Set HalfPlaneLine := {L | (∞ : OnePoint ℂ)∈L.idealEndpoints}

def horizontalHorocycleFamily : Set (Set ℍ) := {S | ∃t : ℝ,0<t ∧ S=horizontalHorocycle t}

theorem mem_parabolicPencilAtInfinity_iff (L : HalfPlaneLine) :
    L∈parabolicPencilAtInfinity ↔ ∃x : ℝ,L=HalfPlaneLine.vertical x :=
  infty_mem_idealEndpoints_iff_vertical L

/-- Source P1 in the actual infinity model, with uniqueness of genuine curve point sets. -/
theorem existsUnique_horizontalHorocycle_through (z : ℍ) :
    ∃!S : Set ℍ,S∈horizontalHorocycleFamily ∧ z∈S := by
  refine ⟨horizontalHorocycle z.im,⟨⟨z.im,z.im_pos,rfl⟩,rfl⟩,?_⟩
  rintro S ⟨⟨t,ht,rfl⟩,hz⟩
  change z.im=t at hz
  rw [←hz]

/-- Source P2 in the actual infinity model. -/
theorem existsUnique_parabolicPencilAtInfinity_through (z : ℍ) :
    ∃!L : HalfPlaneLine,L∈parabolicPencilAtInfinity ∧ z∈L.carrier := by
  refine ⟨HalfPlaneLine.vertical z.re,⟨(mem_parabolicPencilAtInfinity_iff _).mpr ⟨z.re,rfl⟩,rfl⟩,?_⟩
  rintro L ⟨hL,hz⟩
  obtain ⟨x,rfl⟩:=(mem_parabolicPencilAtInfinity_iff L).mp hL
  change z.re=x at hz
  rw [hz]

/-- Source P3 uses genuine Euclidean generalized-circle normal orthogonality. -/
theorem vertical_horizontalHorocycle_orthogonal (x t : ℝ) :
    Mobius.ComplexCirclesOrthogonal (HalfPlaneLine.vertical x).extendedCircle (horizontalHorocycleCircle t) := by
  rw [Mobius.complexCirclesOrthogonal_iff_inversiveProduct_zero,HalfPlaneLine.extendedCircle,
    horizontalHorocycleCircle,complexLine_realModel 1 x one_ne_zero,
    complexLine_realModel Complex.I t Complex.I_ne_zero,Inversive.inversiveProduct_plane_plane]
  simp [Mobius.complexPlaneCoordinates.inner_map_map,Complex.inner]

theorem vertical_reflection_im (x : ℝ) (z : ℍ) :
    ((HalfPlaneLine.vertical x).reflection z).im=z.im := by
  change (verticalReflection x z : ℂ).im=z.im
  rw [verticalReflection_coe]
  simp

/-- Source P4 for the actual reflection point map. -/
theorem vertical_reflection_horizontalHorocycle (x t : ℝ) :
    (HalfPlaneLine.vertical x).reflection '' horizontalHorocycle t=horizontalHorocycle t := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    change ((HalfPlaneLine.vertical x).reflection w).im=t
    rw [vertical_reflection_im]
    exact hw
  · intro hz
    refine ⟨(HalfPlaneLine.vertical x).reflection z,?_,(HalfPlaneLine.vertical x).reflection_involutive z⟩
    change ((HalfPlaneLine.vertical x).reflection z).im=t
    rw [vertical_reflection_im]
    exact hz

/-- Actual distance values between two genuine curve point sets. -/
def hCurvePairDistances (S T : Set ℍ) : Set ℝ := {d | ∃p∈S,∃q∈T,d=dist p q}

def hCurveDistance (S T : Set ℍ) : ℝ := sInf (hCurvePairDistances S T)

theorem hCurvePairDistances_bddBelow (S T : Set ℍ) : BddBelow (hCurvePairDistances S T) := by
  refine ⟨0,?_⟩
  rintro _ ⟨p,_,q,_,rfl⟩
  exact dist_nonneg

theorem hCurveDistance_eq_of_min (S T : Set ℍ) (p q : ℍ) (hp : p∈S) (hq : q∈T)
    (hmin : ∀z∈S,∀w∈T,dist p q≤dist z w) : hCurveDistance S T=dist p q := by
  apply le_antisymm (csInf_le (hCurvePairDistances_bddBelow S T) ⟨p,hp,q,hq,rfl⟩)
  change dist p q≤sInf (hCurvePairDistances S T)
  apply le_csInf (show (hCurvePairDistances S T).Nonempty from ⟨dist p q,p,hp,q,hq,rfl⟩)
  rintro _ ⟨z,hz,w,hw,rfl⟩
  exact hmin z hz w hw

theorem horizontalHorocycle_curveDistance (t u : ℝ) (ht : 0<t) (hu : 0<u) :
    hCurveDistance (horizontalHorocycle t) (horizontalHorocycle u)=|Real.log (t/u)| := by
  let p:=metricProbe 0 t ht
  let q:=metricProbe 0 u hu
  have he : dist p q=dist (Real.log t) (Real.log u):=UpperHalfPlane.dist_of_re_eq rfl
  rw [hCurveDistance_eq_of_min (horizontalHorocycle t) (horizontalHorocycle u) p q rfl rfl]
  · rw [he,Real.dist_eq,←Real.log_div ht.ne' hu.ne']
  · intro z hz w hw
    change z.im=t at hz
    change w.im=u at hw
    rw [he]
    have hh:=UpperHalfPlane.dist_log_im_le z w
    rwa [hz,hw] at hh

/-- Source P5: every actual point has a distance-minimizing mate on the same genuine pencil geodesic. -/
theorem horizontalHorocycle_equidistance (t u : ℝ) (ht : 0<t) (hu : 0<u)
    (p : ℍ) (hp : p∈horizontalHorocycle t) :
    ∃q : ℍ,q∈horizontalHorocycle u ∧
      dist p q=hCurveDistance (horizontalHorocycle t) (horizontalHorocycle u) ∧
      ∃L : HalfPlaneLine,L∈parabolicPencilAtInfinity ∧ p∈L.carrier ∧ q∈L.carrier := by
  let q:=metricProbe p.re u hu
  have he : dist p q=dist (Real.log p.im) (Real.log u):=UpperHalfPlane.dist_of_re_eq rfl
  have hp' : p.im=t:=hp
  refine ⟨q,rfl,?_,HalfPlaneLine.vertical p.re,(mem_parabolicPencilAtInfinity_iff _).mpr ⟨p.re,rfl⟩,rfl,rfl⟩
  rw [he,hp',horizontalHorocycle_curveDistance t u ht hu,Real.dist_eq,←Real.log_div ht.ne' hu.ne']


theorem equidistant_iff_im_coordinates (z a b : ℍ) :
    dist z a=dist z b ↔
      b.im*((z.re-a.re)^2+z.im^2+a.im^2)=a.im*((z.re-b.re)^2+z.im^2+b.im^2) := by
  have hc : Real.cosh (dist z a)=Real.cosh (dist z b) ↔ dist z a=dist z b :=
    ⟨Real.cosh_injOn dist_nonneg dist_nonneg,congrArg Real.cosh⟩
  rw [←hc,UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist',
    div_eq_div_iff (by positivity : 2*z.im*a.im≠0) (by positivity : 2*z.im*b.im≠0)]
  constructor
  · intro he
    apply mul_left_cancel₀ (by positivity : 2*z.im≠0)
    linear_combination he
  · intro he
    linear_combination 2*z.im*he

theorem horizontal_equidistant_iff_of_im_eq {a b : ℍ} (hab : a≠b) (him : a.im=b.im) (z : ℍ) :
    dist z a=dist z b ↔ z.re=(a.re+b.re)/2 := by
  have hre : a.re≠b.re := by
    intro he
    apply hab
    apply UpperHalfPlane.ext
    exact Complex.ext he him
  rw [equidistant_iff_im_coordinates,him]
  have hi : b.im≠0:=b.im_ne_zero
  constructor
  · intro he
    have hf : (b.re-a.re)*(2*z.re-a.re-b.re)=0 := by
      apply mul_left_cancel₀ hi
      linear_combination he
    have hh:=sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hre.symm))
    linarith
  · intro he
    rw [he]
    ring

theorem vertical_equidistance_forces_equal_heights (x : ℝ) (a b : ℍ)
    (h : ∀z∈(HalfPlaneLine.vertical x).carrier,dist z a=dist z b) : a.im=b.im := by
  have h1:=(equidistant_iff_im_coordinates (metricProbe x 1 (by norm_num)) a b).mp
    (h _ rfl)
  have h2:=(equidistant_iff_im_coordinates (metricProbe x 2 (by norm_num)) a b).mp
    (h _ rfl)
  change b.im*((x-a.re)^2+1^2+a.im^2)=a.im*((x-b.re)^2+1^2+b.im^2) at h1
  change b.im*((x-a.re)^2+2^2+a.im^2)=a.im*((x-b.re)^2+2^2+b.im^2) at h2
  nlinarith

theorem same_horizontalHorocycle_iff (a b : ℍ) :
    (∃S∈horizontalHorocycleFamily,a∈S ∧ b∈S) ↔ a.im=b.im := by
  constructor
  · rintro ⟨S,⟨t,ht,rfl⟩,ha,hb⟩
    exact ha.trans hb.symm
  · intro he
    exact ⟨horizontalHorocycle a.im,⟨a.im,a.im_pos,rfl⟩,rfl,he.symm⟩

/-- Source P6 uses the genuine geometric perpendicular bisector. -/
theorem parabolicPencilAtInfinity_perpendicularBisector_iff {a b : ℍ} (hab : a≠b)
    {N : HalfPlaneLine} (hN : IsHPerpendicularBisector N a b) :
    N∈parabolicPencilAtInfinity ↔ ∃S∈horizontalHorocycleFamily,a∈S ∧ b∈S := by
  rw [same_horizontalHorocycle_iff]
  constructor
  · intro hp
    obtain ⟨x,rfl⟩:=(mem_parabolicPencilAtInfinity_iff N).mp hp
    apply vertical_equidistance_forces_equal_heights x a b
    intro z hz
    change z∈HEquidistantLocus a b
    rwa [←hN.carrier_eq hab]
  · intro him
    have he : N=HalfPlaneLine.vertical ((a.re+b.re)/2) := by
      apply HalfPlaneLine.carrier_injective
      rw [hN.carrier_eq hab]
      ext z
      exact horizontal_equidistant_iff_of_im_eq hab him z
    exact (mem_parabolicPencilAtInfinity_iff N).mpr ⟨_,he⟩


theorem horizontalHorocyclicRegion_isHHorocyclicRegion (t : ℝ) (ht : 0<t) :
    IsHHorocyclicRegion (horizontalHorocyclicRegion t) := by
  let r:=1/(t+1)
  have hr : 0<r:=by dsimp [r]; positivity
  have hr1 : r<1:=by dsimp [r]; rw [div_lt_one (by positivity)]; linarith
  have he : (1-r)/r=t:=by dsimp [r]; field_simp; ring
  refine ⟨1,by simp,r,hr,hr1,?_⟩
  rw [discHorocyclicRegion_one_eq_cayley_image r hr hr1,he]

theorem horizontalHorocycleFamily_orthogonal (L : HalfPlaneLine) (hL : L∈parabolicPencilAtInfinity)
    (S : Set ℍ) (hS : S∈horizontalHorocycleFamily) :
    ∃C : Mobius.ComplexGeneralizedCircle,
      S={z : ℍ | ((z : ℂ) : OnePoint ℂ)∈C.val} ∧ Mobius.ComplexCirclesOrthogonal L.extendedCircle C := by
  obtain ⟨x,rfl⟩:=(mem_parabolicPencilAtInfinity_iff L).mp hL
  obtain ⟨t,ht,rfl⟩:=hS
  exact ⟨horizontalHorocycleCircle t,Set.ext (horizontalHorocycle_eq_circleCarrier t),
    vertical_horizontalHorocycle_orthogonal x t⟩

theorem horizontalHorocycleFamily_reflection (L : HalfPlaneLine) (hL : L∈parabolicPencilAtInfinity)
    (S : Set ℍ) (hS : S∈horizontalHorocycleFamily) : L.reflection '' S=S := by
  obtain ⟨x,rfl⟩:=(mem_parabolicPencilAtInfinity_iff L).mp hL
  obtain ⟨t,ht,rfl⟩:=hS
  exact vertical_reflection_horizontalHorocycle x t

theorem horizontalHorocycleFamily_equidistance (S T : Set ℍ)
    (hS : S∈horizontalHorocycleFamily) (hT : T∈horizontalHorocycleFamily) (p : ℍ) (hp : p∈S) :
    ∃q : ℍ,q∈T ∧ dist p q=hCurveDistance S T ∧
      ∃L : HalfPlaneLine,L∈parabolicPencilAtInfinity ∧ p∈L.carrier ∧ q∈L.carrier := by
  obtain ⟨t,ht,rfl⟩:=hS
  obtain ⟨u,hu,rfl⟩:=hT
  exact horizontalHorocycle_equidistance t u ht hu p hp

end
end LowDimensionalTopology.Geometry.Hyperbolic
