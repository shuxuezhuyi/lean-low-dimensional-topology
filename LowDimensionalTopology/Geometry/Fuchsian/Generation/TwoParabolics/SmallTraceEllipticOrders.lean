/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.TwoParabolicTraceClassification
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPointHeights
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The exact fifth-angle estimate needed to exclude every larger
finite elliptic order from a nearest unit-translation trace. -/
theorem tan_pi_div_five_sq_lt_three_quarters : (Real.tan (Real.pi/5))^2<3/4 := by
  have hco:0<Real.cos (Real.pi/5):=Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have hcos:(4:ℝ)/7<(Real.cos (Real.pi/5))^2:=by
    rw [Real.cos_pi_div_five]
    have hs:2≤Real.sqrt (5:ℝ):=by
      nlinarith [Real.sq_sqrt (by norm_num:0≤(5:ℝ)),Real.sqrt_nonneg (5:ℝ)]
    nlinarith [Real.sq_sqrt (by norm_num:0≤(5:ℝ))]
  have htc:Real.tan (Real.pi/5)*Real.cos (Real.pi/5)=Real.sin (Real.pi/5):=by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have hid:(1+(Real.tan (Real.pi/5))^2)*(Real.cos (Real.pi/5))^2=1:=by
    have hs: (Real.tan (Real.pi/5))^2*(Real.cos (Real.pi/5))^2=(Real.sin (Real.pi/5))^2:=by
      rw [←mul_pow,htc]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi/5)]
  nlinarith [mul_pos (sub_pos.mpr hcos) (show 0<1+(Real.tan (Real.pi/5))^2 by positivity)]

/-- The genuine fixed-center trace identity and sharp height estimate
exclude orders at least five when the lower-left entry is below two. -/
theorem small_trace_height_order_le_four (c t y:ℝ) (n:ℕ)
    (hc:0<c) (hc2:c<2) (hy:0<y) (ht:|t|≤c/2)
    (hid:4*c^2*y^2+t^2=4)
    (hheight:3≤n→y≤Real.tan (Real.pi/n)/2) : n≤4 := by
  by_contra hn
  have hn5:5≤n:=by omega
  have hnR:(5:ℝ)≤n:=by exact_mod_cast hn5
  have hangle:Real.pi/(n:ℝ)≤Real.pi/5:=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hnR
  have harg:0<Real.pi/(n:ℝ):=div_pos Real.pi_pos (by linarith only [hnR])
  have htan:Real.tan (Real.pi/(n:ℝ))≤Real.tan (Real.pi/5):=
    Real.strictMonoOn_tan.monotoneOn
      ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩ hangle
  have hybound:2*y≤Real.tan (Real.pi/5):=by
    have h:=hheight (by omega)
    linarith only [h,htan]
  have hysq:4*y^2<3/4:=by
    have h:=mul_self_le_mul_self (by positivity:0≤2*y) hybound
    nlinarith [tan_pi_div_five_sq_lt_three_quarters]
  have htsq:t^2≤c^2/4:=by
    have h:=sq_le_sq₀ (abs_nonneg t) (by positivity:0≤c/2) |>.mpr ht
    nlinarith only [h,sq_abs t]
  have hcSq:c^2<4:=by nlinarith only [hc,hc2]
  have hm:=mul_lt_mul_of_pos_left hysq (sq_pos_of_pos hc)
  nlinarith only [hid,htsq,hcSq,hm]

/-- The complete small-order cosine list has a strict unit trace
gap outside order two, with the primitive integer index enforced. -/
theorem small_order_trace_cosine_gap (r m:ℕ) (t:ℝ)
    (hr2:2≤r) (hr4:r≤4) (hm0:0<m) (hmr:m<r) (hcop:m.Coprime r)
    (htrace:t^2=4*(Real.cos (Real.pi*(m:ℝ)/r))^2) (htr:|t|<1) :
    t=0 ∧ r=2 := by
  have htsq:t^2<1:=by
    have h:=(sq_lt_sq₀ (abs_nonneg t) (by norm_num:0≤(1:ℝ))).mpr htr
    simpa only [sq_abs,one_pow] using h
  have hr:r=2 ∨ r=3 ∨ r=4:=by omega
  rcases hr with rfl|rfl|rfl
  · have hm:m=1:=by omega
    subst m
    norm_num only [Nat.cast_ofNat, mul_one, Real.cos_pi_div_two, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, mul_zero] at htrace
    exact ⟨by nlinarith only [htrace],rfl⟩
  · have hm:m=1 ∨ m=2:=by omega
    rcases hm with rfl|rfl
    · norm_num only [Nat.cast_ofNat,mul_one,Real.cos_pi_div_three] at htrace
      nlinarith only [htrace,htsq]
    · norm_num only [Nat.cast_ofNat] at htrace
      rw [show Real.pi*2/3=Real.pi-Real.pi/3 by ring,Real.cos_pi_sub,Real.cos_pi_div_three] at htrace
      nlinarith only [htrace,htsq]
  · have hm2:m≠2:=by
      intro he
      subst m
      norm_num [Nat.coprime_iff_gcd_eq_one] at hcop
    have hm:m=1 ∨ m=3:=by omega
    rcases hm with rfl|rfl
    · norm_num only [Nat.cast_ofNat,mul_one,Real.cos_pi_div_four] at htrace
      nlinarith [htrace,htsq,Real.sq_sqrt (by norm_num:0≤(2:ℝ))]
    · norm_num only [Nat.cast_ofNat] at htrace
      rw [show Real.pi*3/4=Real.pi-Real.pi/4 by ring,Real.cos_pi_sub,Real.cos_pi_div_four] at htrace
      nlinarith [htrace,htsq,Real.sq_sqrt (by norm_num:0≤(2:ℝ))]

/-- Finite order at most four leaves a unit trace gap away from the
actual order-two case; trace and order refer to the genuine Mobius map. -/
theorem realSL_small_trace_small_order_halfTurn (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hne:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1)
    (hfin:IsOfFinOrder (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hord:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)≤4) (htr:|Matrix.trace A.val|<1) :
    Matrix.trace A.val=0 ∧ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=2 := by
  obtain ⟨r,m,hr,hr2,hm0,hmr,hcop,htrace⟩:=realSL_finite_order_trace_cosine A hne hfin
  have hr4:r≤4:=hr ▸ hord
  have h:=small_order_trace_cosine_gap r m (Matrix.trace A.val) hr2 hr4 hm0 hmr hcop htrace htr
  exact ⟨h.1,hr.symm.trans h.2⟩

/-- For an actual discrete original half-plane group containing the
unit translation, every genuine nearest-trace matrix with lower-left
entry between zero and two is an actual half-turn of trace zero. -/
theorem realSL_nearest_trace_halfTurn (H:Subgroup Mobius.complexMobiusGroup)
    (hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hT:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (hpres:∀f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H)
    (hc:A 1 0≠0) (hc2:|A 1 0|<2) (ht:|Matrix.trace A.val|≤|A 1 0|/2) :
    Matrix.trace A.val=0 ∧ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=2 := by
  have htr:|Matrix.trace A.val|<1:=by linarith only [ht,hc2]
  have hne:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1:=by
    intro he
    have ha:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (1:Matrix.SpecialLinearGroup (Fin 2) ℝ):=by
      simpa only [map_one] using he
    rcases (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_iff_sign A 1).mp ha with ha|ha
    all_goals
      have h:=congrArg (fun B:Matrix.SpecialLinearGroup (Fin 2) ℝ=>B 1 0) ha
      norm_num at h
      first | exact hc h | exact hc h.symm
  have hs:(Matrix.trace A.val)^2<4:=by
    have h:=sq_lt_sq₀ (abs_nonneg _) (by norm_num:0≤(1:ℝ)) |>.mpr htr
    nlinarith only [h,sq_abs (Matrix.trace A.val)]
  have hEll:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hne).mpr hs
  let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A hs
  have hfix:A•z=z:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A hs z).mpr rfl
  have hi:=realSL_fixed_trace_height_identity A z hfix
  have ho:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)≤4:=small_trace_height_order_le_four
    |A 1 0| (Matrix.trace A.val) z.im (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (abs_pos.mpr hc) hc2 z.im_pos ht (by simpa only [sq_abs] using hi)
    (fun hn=>realSL_elliptic_center_height H hd hT hpres A hAH hEll hn)
  exact realSL_small_trace_small_order_halfTurn A hne
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elliptic_finiteOrder H hd _ hAH hEll) ho htr

end LowDimensionalTopology.Geometry.Fuchsian
