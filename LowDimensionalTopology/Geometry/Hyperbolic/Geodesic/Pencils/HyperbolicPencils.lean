/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.EllipticPencils
@[expose] public section
open Set Filter
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint ComplexConjugate Topology
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Inversive
noncomputable section

/-- An individual genuine upper-half-plane ray, including the zero-offset axis itself. -/
def imaginaryAxisHypercycleBranch (c : ℝ) : Set ℍ := {z | z.re=c*z.im}

def imaginaryAxisHypercycleBranchFamily : Set (Set ℍ) := {S | ∃c : ℝ,S=imaginaryAxisHypercycleBranch c}

def hHyperbolicPencil (axis : HalfPlaneLine) : Set HalfPlaneLine := {L | L.Orthogonal axis}

theorem hypercycleBranchNormal_ne_zero (c : ℝ) : 1-(c : ℂ)*Complex.I≠0 := by
  intro he
  have hh:=congrArg Complex.re he
  simp at hh

def hypercycleBranchCircle (c : ℝ) : Mobius.ComplexGeneralizedCircle :=
  ⟨Mobius.complexLine (1-(c : ℂ)*Complex.I) 0,Mobius.complexLine_isGeneralized _ 0 (hypercycleBranchNormal_ne_zero c)⟩

theorem imaginaryAxisHypercycleBranch_eq_circleCarrier (c : ℝ) :
    imaginaryAxisHypercycleBranch c=halfPlaneCircleCarrier (hypercycleBranchCircle c) := by
  ext z
  change z.re=c*z.im ↔ ((z : ℂ) : OnePoint ℂ)∈Mobius.complexLine (1-(c : ℂ)*Complex.I) 0
  rw [Mobius.complexLine_coe,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
  simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
    zero_sub,sub_zero,add_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  constructor <;> intro h <;> nlinarith

theorem imaginaryAxisHypercycleBranch_zero :
    imaginaryAxisHypercycleBranch 0=(HalfPlaneLine.vertical 0).carrier := by
  ext z
  change z.re=0*z.im ↔ z.re=0
  rw [zero_mul]

theorem mem_hHyperbolicPencil_imaginaryAxis_iff (L : HalfPlaneLine) :
    L∈hHyperbolicPencil (.vertical 0) ↔ ∃(r : ℝ)(hr : 0<r),L=.circle 0 r hr :=
  orthogonal_imaginary_axis_iff_circle L

theorem existsUnique_imaginaryAxisHypercycleBranch_through (z : ℍ) :
    ∃!S : Set ℍ,S∈imaginaryAxisHypercycleBranchFamily ∧ z∈S := by
  have hz : z.re=(z.re/z.im)*z.im:=by field_simp
  refine ⟨imaginaryAxisHypercycleBranch (z.re/z.im),⟨⟨_,rfl⟩,hz⟩,?_⟩
  rintro S ⟨⟨c,rfl⟩,hc⟩
  change z.re=c*z.im at hc
  have he : z.re/z.im=c:=by rw [hc]; field_simp
  rw [he]

theorem existsUnique_hHyperbolicPencil_imaginaryAxis_through (z : ℍ) :
    ∃!L : HalfPlaneLine,L∈hHyperbolicPencil (.vertical 0) ∧ z∈L.carrier := by
  have hn : 0<‖(z : ℂ)‖:=norm_pos_iff.mpr z.ne_zero
  refine ⟨.circle 0 ‖(z : ℂ)‖ hn,⟨?_,?_⟩,?_⟩
  · exact (mem_hHyperbolicPencil_imaginaryAxis_iff _).mpr ⟨_,hn,rfl⟩
  · change ‖(z : ℂ)-(0 : ℂ)‖=‖(z : ℂ)‖
    rw [sub_zero]
  · rintro L ⟨hL,hz⟩
    obtain ⟨r,hr,rfl⟩:=(mem_hHyperbolicPencil_imaginaryAxis_iff L).mp hL
    change ‖(z : ℂ)-(0 : ℂ)‖=r at hz
    rw [sub_zero] at hz
    subst r
    rfl

theorem concentricCircle_hypercycleBranch_orthogonal (r c : ℝ) (hr : 0<r) :
    Mobius.ComplexCirclesOrthogonal (HalfPlaneLine.circle 0 r hr).extendedCircle (hypercycleBranchCircle c) := by
  rw [Mobius.complexCirclesOrthogonal_iff_inversiveProduct_zero,HalfPlaneLine.extendedCircle,hypercycleBranchCircle,
    complexCircle_realModel _ _ hr,complexLine_realModel _ _ (hypercycleBranchNormal_ne_zero
      c),Inversive.inversiveProduct_sphere_plane]
  simp

theorem concentricCircle_reflection_hypercycleBranch_mem (r c : ℝ) (hr : 0<r) (z : ℍ)
    (hz : z∈imaginaryAxisHypercycleBranch c) :
    (HalfPlaneLine.circle 0 r hr).reflection z∈imaginaryAxisHypercycleBranch c := by
  change (circleReflection 0 r hr z : ℂ).re=c*(circleReflection 0 r hr z : ℂ).im
  rw [circleReflection_coe]
  rw [←Complex.ofReal_pow]
  simp only [Complex.ofReal_zero,zero_add,sub_zero,Complex.div_re,Complex.div_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im,zero_mul,
    mul_neg,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  change z.re=c*z.im at hz
  rw [hz]
  ring

theorem concentricCircle_reflection_hypercycleBranch (r c : ℝ) (hr : 0<r) :
    (HalfPlaneLine.circle 0 r hr).reflection '' imaginaryAxisHypercycleBranch c=imaginaryAxisHypercycleBranch c := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact concentricCircle_reflection_hypercycleBranch_mem r c hr w hw
  · intro hz
    exact ⟨(HalfPlaneLine.circle 0 r hr).reflection z,
      concentricCircle_reflection_hypercycleBranch_mem r c hr z hz,(HalfPlaneLine.circle 0 r
        hr).reflection_involutive z⟩

theorem imaginaryAxisHypercycleBranch_pointDist_sinh (c : ℝ) (z : ℍ) (hz : z∈imaginaryAxisHypercycleBranch c) :
    Real.sinh ((HalfPlaneLine.vertical 0).pointDist z)=|c| := by
  rw [verticalLine_pointDist_sinh]
  change z.re=c*z.im at hz
  rw [sub_zero,hz,abs_mul,abs_of_pos z.im_pos,mul_div_cancel_right₀ _ z.im_ne_zero]


theorem halfPlane_norm_sq (z : ℍ) : ‖(z : ℂ)‖^2=z.re^2+z.im^2 := by
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  change z.re*z.re+z.im*z.im=z.re^2+z.im^2
  ring

theorem cosh_dist_norm (z w : ℍ) :
    Real.cosh (dist z w)=(‖(z : ℂ)‖^2+‖(w : ℂ)‖^2-2*z.re*w.re)/(2*z.im*w.im) := by
  rw [UpperHalfPlane.cosh_dist',halfPlane_norm_sq,halfPlane_norm_sq]
  congr 1
  ring

theorem imaginaryAxisHypercycleBranch_positive_radial (c : ℝ) (p z : ℍ)
    (hp : p∈imaginaryAxisHypercycleBranch c) (hz : z∈imaginaryAxisHypercycleBranch c) :
    ∃a : ℝ,0<a ∧ (z : ℂ)=(a : ℂ)*(p : ℂ) := by
  refine ⟨z.im/p.im,div_pos z.im_pos p.im_pos,?_⟩
  apply Complex.ext
  · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,UpperHalfPlane.coe_re]
    change p.re=c*p.im at hp
    change z.re=c*z.im at hz
    rw [hp,hz]
    field_simp
  · simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,UpperHalfPlane.coe_im]
    field_simp

theorem exists_imaginaryAxisHypercycleBranch_point_norm (c R : ℝ) (hR : 0<R) :
    ∃z : ℍ,z∈imaginaryAxisHypercycleBranch c ∧ ‖(z : ℂ)‖=R := by
  let s:=R/Real.sqrt (c^2+1)
  have hroot : 0<Real.sqrt (c^2+1):=Real.sqrt_pos.mpr (by positivity)
  have hs : 0<s:=div_pos hR hroot
  let z:=metricProbe (c*s) s hs
  refine ⟨z,rfl,?_⟩
  have hroot2:=Real.sq_sqrt (by positivity : 0≤c^2+1)
  have hn : ‖(z : ℂ)‖^2=R^2 := by
    rw [halfPlane_norm_sq]
    change (c*s)^2+s^2=R^2
    dsimp [s]
    field_simp
    nlinarith only [hroot2]
  nlinarith [norm_nonneg (z : ℂ)]

/-- Actual hyperbolic-distance comparison of arbitrary positive radial scalings. -/
theorem cosh_dist_positive_radial_lower (p q z w : ℍ) (hn : ‖(p : ℂ)‖=‖(q : ℂ)‖)
    (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (hz : (z : ℂ)=(a : ℂ)*(p : ℂ)) (hw : (w : ℂ)=(b : ℂ)*(q : ℂ)) :
    Real.cosh (dist p q)≤Real.cosh (dist z w) := by
  have hzre : z.re=a*p.re:=by simpa using congrArg Complex.re hz
  have hzim : z.im=a*p.im:=by simpa using congrArg Complex.im hz
  have hwre : w.re=b*q.re:=by simpa using congrArg Complex.re hw
  have hwim : w.im=b*q.im:=by simpa using congrArg Complex.im hw
  have hzn : ‖(z : ℂ)‖=a*‖(p : ℂ)‖:=by rw [hz,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
  have hwn : ‖(w : ℂ)‖=b*‖(q : ℂ)‖:=by rw [hw,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb]
  have he : Real.cosh (dist z w)-Real.cosh (dist p q)=
      (a-b)^2*‖(p : ℂ)‖^2/(2*a*b*p.im*q.im) := by
    rw [cosh_dist_norm,cosh_dist_norm,hzn,hwn,←hn,hzre,hzim,hwre,hwim]
    field_simp
    ring
  have hnon : 0≤Real.cosh (dist z w)-Real.cosh (dist p q) := by
    rw [he]
    positivity
  linarith

theorem imaginaryAxisHypercycleBranch_radial_minimizes (c d : ℝ) (p q : ℍ)
    (hp : p∈imaginaryAxisHypercycleBranch c) (hq : q∈imaginaryAxisHypercycleBranch d)
    (hn : ‖(p : ℂ)‖=‖(q : ℂ)‖) :
    ∀z∈imaginaryAxisHypercycleBranch c,∀w∈imaginaryAxisHypercycleBranch d,dist p q≤dist z w := by
  intro z hz w hw
  obtain ⟨a,ha,hza⟩:=imaginaryAxisHypercycleBranch_positive_radial c p z hp hz
  obtain ⟨b,hb,hwb⟩:=imaginaryAxisHypercycleBranch_positive_radial d q w hq hw
  have hcosh:=cosh_dist_positive_radial_lower p q z w hn a b ha hb hza hwb
  rw [Real.cosh_le_cosh,abs_of_nonneg dist_nonneg,abs_of_nonneg dist_nonneg] at hcosh
  exact hcosh

/-- P5: a genuine minimum of the actual two-curve distance lies on one concentric pencil circle. -/
theorem imaginaryAxisHypercycleBranch_equidistance (c d : ℝ) (p : ℍ) (hp : p∈imaginaryAxisHypercycleBranch c) :
    ∃q : ℍ,q∈imaginaryAxisHypercycleBranch d ∧
      dist p q=hCurveDistance (imaginaryAxisHypercycleBranch c) (imaginaryAxisHypercycleBranch d) ∧
      ∃L : HalfPlaneLine,L∈hHyperbolicPencil (.vertical 0) ∧ p∈L.carrier ∧ q∈L.carrier := by
  have hn : 0<‖(p : ℂ)‖:=norm_pos_iff.mpr p.ne_zero
  obtain ⟨q,hq,hqn⟩:=exists_imaginaryAxisHypercycleBranch_point_norm d ‖(p : ℂ)‖ hn
  refine ⟨q,hq,?_,.circle 0 ‖(p : ℂ)‖ hn,
    (mem_hHyperbolicPencil_imaginaryAxis_iff _).mpr ⟨_,hn,rfl⟩,?_,?_⟩
  · symm
    exact hCurveDistance_eq_of_min _ _ p q hp hq
      (imaginaryAxisHypercycleBranch_radial_minimizes c d p q hp hq hqn.symm)
  · change ‖(p : ℂ)-(0 : ℂ)‖=‖(p : ℂ)‖
    rw [sub_zero]
  · change ‖(q : ℂ)-(0 : ℂ)‖=‖(p : ℂ)‖
    rwa [sub_zero]


theorem same_imaginaryAxisHypercycleBranch_iff (a b : ℍ) :
    (∃S∈imaginaryAxisHypercycleBranchFamily,a∈S ∧ b∈S) ↔ a.re/a.im=b.re/b.im := by
  constructor
  · rintro ⟨S,⟨c,rfl⟩,ha,hb⟩
    change a.re=c*a.im at ha
    change b.re=c*b.im at hb
    rw [ha,hb]
    field_simp
  · intro he
    refine ⟨imaginaryAxisHypercycleBranch (a.re/a.im),⟨_,rfl⟩,?_,?_⟩
    · change a.re=(a.re/a.im)*a.im
      field_simp
    · change b.re=(a.re/a.im)*b.im
      rw [he]
      field_simp

theorem same_branch_equidistant_circle {a b : ℍ} (hab : a≠b) (c : ℝ)
    (ha : a∈imaginaryAxisHypercycleBranch c) (hb : b∈imaginaryAxisHypercycleBranch c) (z : ℍ) :
    dist z a=dist z b ↔ ‖(z : ℂ)‖=Real.sqrt ((c^2+1)*a.im*b.im) := by
  change a.re=c*a.im at ha
  change b.re=c*b.im at hb
  have hi : a.im≠b.im := by
    intro he
    apply hab
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change a.re=b.re
      rw [ha,hb,he]
    · exact he
  have hpos : 0<(c^2+1)*a.im*b.im:=by positivity
  have hsqrt:=Real.sq_sqrt hpos.le
  have hsqrtpos:=Real.sqrt_pos.mpr hpos
  rw [equidistant_iff_im_coordinates,ha,hb,←sq_eq_sq₀ (norm_nonneg _) hsqrtpos.le,hsqrt,halfPlane_norm_sq]
  constructor
  · intro he
    have hf : (b.im-a.im)*(z.re^2+z.im^2-(c^2+1)*a.im*b.im)=0:=by linear_combination he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hi.symm))
  · intro he
    linear_combination (b.im-a.im)*he

/-- A genuine concentric bisector forces the two points to lie on the same actual ray branch. -/
theorem concentric_perpendicularBisector_same_branch {a b : ℍ} (hab : a≠b)
    (r : ℝ) (hr : 0<r) (hN : IsHPerpendicularBisector (.circle 0 r hr) a b) :
    a.re/a.im=b.re/b.im := by
  let B:=2*(a.im*b.re-b.im*a.re)
  let C:=(b.im-a.im)*r^2+b.im*(a.re^2+a.im^2)-a.im*(b.re^2+b.im^2)
  have hzero : ∀z∈(HalfPlaneLine.circle 0 r hr).carrier,(0 : ℝ)*z.re^2+B*z.re+C=0 := by
    intro z hz
    have he : dist z a=dist z b := by
      change z∈HEquidistantLocus a b
      rwa [←hN.carrier_eq hab]
    have he':=(equidistant_iff_im_coordinates z a b).mp he
    have hc:=norm_sub_real_eq_radius_sq hz
    change (z.re-0)^2+z.im^2=r^2 at hc
    dsimp only [B,C]
    linear_combination he'-(b.im-a.im)*hc
  rcases (HalfPlaneLine.circle 0 r hr).quadratic_re_vanish 0 B C hzero with ⟨d,he⟩ | ⟨_,hB,_⟩
  · cases he
  · apply (div_eq_div_iff a.im_ne_zero b.im_ne_zero).mpr
    dsimp [B] at hB
    nlinarith

/-- P6 for actual concentric-pencil geodesics and genuine individual hypercycle branches. -/
theorem imaginaryAxisHyperbolicPencil_perpendicularBisector_iff {a b : ℍ} (hab : a≠b)
    {N : HalfPlaneLine} (hN : IsHPerpendicularBisector N a b) :
    N∈hHyperbolicPencil (.vertical 0) ↔
      ∃S∈imaginaryAxisHypercycleBranchFamily,a∈S ∧ b∈S := by
  constructor
  · intro hp
    obtain ⟨r,hr,rfl⟩:=(mem_hHyperbolicPencil_imaginaryAxis_iff N).mp hp
    exact (same_imaginaryAxisHypercycleBranch_iff a b).mpr
      (concentric_perpendicularBisector_same_branch hab r hr hN)
  · rintro ⟨S,⟨c,rfl⟩,ha,hb⟩
    let r:=Real.sqrt ((c^2+1)*a.im*b.im)
    have hr : 0<r:=Real.sqrt_pos.mpr (by positivity)
    have he : N=HalfPlaneLine.circle 0 r hr := by
      apply HalfPlaneLine.carrier_injective
      rw [hN.carrier_eq hab]
      ext z
      change dist z a=dist z b ↔ ‖(z : ℂ)-(0 : ℂ)‖=r
      rw [sub_zero]
      exact same_branch_equidistant_circle hab c ha hb z
    exact (mem_hHyperbolicPencil_imaginaryAxis_iff N).mpr ⟨r,hr,he⟩


theorem imaginaryAxisHypercycleBranch_eq_arg (c : ℝ) :
    imaginaryAxisHypercycleBranch c={z : ℍ | Complex.arg (z : ℂ)=Complex.arg (metricProbe c 1 (by norm_num) : ℂ)} := by
  let p:=metricProbe c 1 (by norm_num)
  ext z
  constructor
  · intro hz
    obtain ⟨a,ha,he⟩:=imaginaryAxisHypercycleBranch_positive_radial c p z (by change c=c*1; ring) hz
    change Complex.arg (z : ℂ)=Complex.arg (p : ℂ)
    rw [he,Complex.arg_real_mul _ ha]
  · intro hz
    change Complex.arg (z : ℂ)=Complex.arg (p : ℂ) at hz
    have he:=((Complex.arg_eq_arg_iff p.ne_zero z.ne_zero).mp hz.symm).symm
    rw [←Complex.ofReal_div] at he
    have hre:=congrArg Complex.re he
    have him:=congrArg Complex.im he
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,add_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im] at hre him
    have hpR : p.re=c:=rfl
    have hpI : p.im=1:=rfl
    rw [hpR] at hre
    rw [hpI,mul_one] at him
    change z.re=c*z.im
    rw [hre,him]
    ring

/-- The genuine full unsigned distance level is two ray branches, with the axis as their common zero case. -/
theorem imaginaryAxis_distance_sinh_level_two_branches (c : ℝ) :
    {z : ℍ | Real.sinh ((HalfPlaneLine.vertical 0).pointDist z)=|c|}=
      imaginaryAxisHypercycleBranch c∪imaginaryAxisHypercycleBranch (-c) := by
  ext z
  change Real.sinh ((HalfPlaneLine.vertical 0).pointDist z)=|c| ↔ z.re=c*z.im ∨ z.re=(-c)*z.im
  rw [verticalLine_pointDist_sinh,sub_zero,show z.im=|z.im| from (abs_of_pos z.im_pos).symm,
    ←abs_div,abs_eq_abs]
  simp only [abs_of_pos z.im_pos,div_eq_iff z.im_ne_zero]

def hypercycleBranchParam (c t : ℝ) : ℍ :=
  metricProbe (c*Real.exp t) (Real.exp t) (Real.exp_pos t)

theorem hypercycleBranchParam_extended_affine (c t : ℝ) :
    Mobius.affineHomeomorph (1-(c : ℂ)*Complex.I) 0 (hypercycleBranchNormal_ne_zero c)
      (extendedHalfPlanePoint (imaginaryAxisParam t))=extendedHalfPlanePoint (hypercycleBranchParam c t) := by
  change Mobius.affineHomeomorph (1-(c : ℂ)*Complex.I) 0 _
    (((imaginaryAxisParam t : ℍ) : ℂ) : OnePoint ℂ)=_
  rw [Mobius.affineHomeomorph_coe]
  apply congrArg ((↑) : ℂ → OnePoint ℂ)
  apply Complex.ext <;> simp [hypercycleBranchParam,metricProbe,imaginaryAxisParam]

theorem hypercycleBranchParam_tendsto_zero (c : ℝ) :
    Tendsto (fun t : ℝ => extendedHalfPlanePoint (hypercycleBranchParam c t)) atBot (𝓝 ((0 : ℂ) : OnePoint ℂ)) := by
  let f:=Mobius.affineHomeomorph (1-(c : ℂ)*Complex.I) 0 (hypercycleBranchNormal_ne_zero c)
  have hh:=f.continuous.continuousAt.tendsto.comp imaginaryAxisParam_tendsto_zero
  change Tendsto (fun t : ℝ => f (extendedHalfPlanePoint (imaginaryAxisParam t))) atBot
    (𝓝 (f ((0 : ℂ) : OnePoint ℂ))) at hh
  dsimp only [f] at hh
  simp only [hypercycleBranchParam_extended_affine] at hh
  rw [Mobius.affineHomeomorph_coe,mul_zero,add_zero] at hh
  exact hh

theorem hypercycleBranchParam_tendsto_infty (c : ℝ) :
    Tendsto (fun t : ℝ => extendedHalfPlanePoint (hypercycleBranchParam c t)) atTop (𝓝 (∞ : OnePoint ℂ)) := by
  let f:=Mobius.affineHomeomorph (1-(c : ℂ)*Complex.I) 0 (hypercycleBranchNormal_ne_zero c)
  have hh:=f.continuous.continuousAt.tendsto.comp imaginaryAxisParam_tendsto_infty
  change Tendsto (fun t : ℝ => f (extendedHalfPlanePoint (imaginaryAxisParam t))) atTop (𝓝 (f ∞)) at hh
  dsimp only [f] at hh
  simpa only [hypercycleBranchParam_extended_affine,Mobius.affineHomeomorph_infty] using hh

/-- The actual compactified curve closure has exactly the axis's two true ideal ends. -/
theorem imaginaryAxisHypercycleBranch_idealEndpoints (c : ℝ) :
    hTraceIdealEndpoints (imaginaryAxisHypercycleBranch c)={((0 : ℂ) : OnePoint ℂ),∞} := by
  have hzero : ((0 : ℂ) : OnePoint ℂ)∈closure (extendedHalfPlanePoint '' imaginaryAxisHypercycleBranch c) :=
    mem_closure_of_tendsto (hypercycleBranchParam_tendsto_zero c)
      (Filter.Eventually.of_forall (fun t => ⟨hypercycleBranchParam c t,rfl,rfl⟩))
  have hinfty : (∞ : OnePoint ℂ)∈closure (extendedHalfPlanePoint '' imaginaryAxisHypercycleBranch c) :=
    mem_closure_of_tendsto (hypercycleBranchParam_tendsto_infty c)
      (Filter.Eventually.of_forall (fun t => ⟨hypercycleBranchParam c t,rfl,rfl⟩))
  ext z
  induction z using OnePoint.rec with
  | infty => simp [hTraceIdealEndpoints,halfPlaneIdealBoundary,hinfty]
  | coe z =>
    rw [hTraceIdealEndpoints_finite_iff]
    simp only [mem_insert_iff,mem_singleton_iff,OnePoint.coe_eq_coe,OnePoint.coe_ne_infty,or_false]
    constructor
    · rintro ⟨hz,him⟩
      have hc : z∈{w : ℂ | w.re=c*w.im}:=by
        apply closure_minimal ?_ (isClosed_eq Complex.continuous_re (continuous_const.mul Complex.continuous_im)) hz
        rintro _ ⟨u,hu,rfl⟩
        exact hu
      apply Complex.ext
      · change z.re=0
        change z.re=c*z.im at hc
        rw [hc,him,mul_zero]
      · exact him
    · rintro rfl
      exact ⟨(hTraceIdealEndpoints_finite_iff _ 0).mp ⟨hzero,by simp [coe_mem_halfPlaneIdealBoundary]⟩ |>.1,rfl⟩


/-- An individual actual hypercycle branch is the nonempty H portion of a genuine
completed circle with exactly the designated axis's two ideal intersections. -/
def IsHHypercycleBranch (axis : HalfPlaneLine) (S : Set ℍ) : Prop :=
  ∃C : Mobius.ComplexGeneralizedCircle,C.val∩halfPlaneIdealBoundary=axis.idealEndpoints ∧
    S=halfPlaneCircleCarrier C ∧ S.Nonempty

theorem hypercycleBranchCircle_ideal_intersection (c : ℝ) :
    (hypercycleBranchCircle c).val∩halfPlaneIdealBoundary=(HalfPlaneLine.vertical 0).idealEndpoints := by
  rw [vertical_idealEndpoints]
  ext z
  induction z using OnePoint.rec with
  | infty => simp [hypercycleBranchCircle,halfPlaneIdealBoundary]
  | coe z =>
    rw [mem_inter_iff,coe_mem_halfPlaneIdealBoundary]
    change (((z : OnePoint ℂ)∈Mobius.complexLine (1-(c : ℂ)*Complex.I) 0) ∧ z.im=0) ↔ _
    rw [Mobius.complexLine_coe,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
      zero_sub,sub_zero,add_zero,mem_insert_iff,mem_singleton_iff,OnePoint.coe_eq_coe,
      OnePoint.coe_ne_infty,or_false]
    constructor
    · rintro ⟨hr,hi⟩
      apply Complex.ext
      · change z.re=0
        rw [hi,zero_mul,add_zero] at hr
        exact hr
      · exact hi
    · rintro rfl
      simp

theorem imaginaryAxisHypercycleBranch_isHHypercycleBranch (c : ℝ) :
    IsHHypercycleBranch (.vertical 0) (imaginaryAxisHypercycleBranch c) := by
  refine ⟨hypercycleBranchCircle c,hypercycleBranchCircle_ideal_intersection c,
    imaginaryAxisHypercycleBranch_eq_circleCarrier c,metricProbe c 1 (by norm_num),?_⟩
  change c=c*1
  ring

/-- The intrinsic actual-circle family is exhaustive in the source's concentric normal model. -/
theorem isHHypercycleBranch_imaginaryAxis_iff (S : Set ℍ) :
    IsHHypercycleBranch (.vertical 0) S ↔ S∈imaginaryAxisHypercycleBranchFamily := by
  constructor
  · rintro ⟨C,hC,rfl,hne⟩
    rw [vertical_idealEndpoints] at hC
    have hinf : (∞ : OnePoint ℂ)∈C.val:=by
      have hh : (∞ : OnePoint ℂ)∈C.val∩halfPlaneIdealBoundary:=by rw [hC]; simp
      exact hh.1
    have h0 : ((0 : ℂ) : OnePoint ℂ)∈C.val:=by
      have hh : ((0 : ℂ) : OnePoint ℂ)∈C.val∩halfPlaneIdealBoundary:=by rw [hC]; simp
      exact hh.1
    rcases (Mobius.isComplexGeneralizedCircle_iff C.val).mp C.property with ⟨c,r,hr,he⟩ | ⟨a,t,ha,he⟩
    · rw [he] at hinf
      exact False.elim (Mobius.complexCircle_infty c r hinf)
    · rw [he,Mobius.complexLine_coe] at h0
      have ht : t=0:=by simpa using h0.symm
      rw [ht] at he
      have hare : a.re≠0 := by
        intro har
        have hp : ((1 : ℂ) : OnePoint ℂ)∈C.val∩halfPlaneIdealBoundary := by
          refine ⟨?_,by simp [coe_mem_halfPlaneIdealBoundary]⟩
          rw [he,Mobius.complexLine_coe,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
          simpa using har
        rw [hC] at hp
        simp at hp
      refine ⟨-a.im/a.re,?_⟩
      ext z
      change ((z : ℂ) : OnePoint ℂ)∈C.val ↔ z.re=(-a.im/a.re)*z.im
      rw [he, Mobius.complexLine_coe, _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,
        div_mul_eq_mul_div, eq_div_iff hare]
      simp only [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
      constructor <;> intro h <;> nlinarith
  · rintro ⟨c,rfl⟩
    exact imaginaryAxisHypercycleBranch_isHHypercycleBranch c

end
end LowDimensionalTopology.Geometry.Hyperbolic
