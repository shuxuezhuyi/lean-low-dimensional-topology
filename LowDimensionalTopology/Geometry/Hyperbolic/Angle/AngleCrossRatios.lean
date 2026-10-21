/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.BoundaryOrder

/-!
# Actual tangent angles and ideal-endpoint cross-ratios
-/
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem HRayAt.re_mem_closure_of_idealEndpoint {p : ℍ} (R : HRayAt p) (a : ℝ)
    (ha : R.idealEndpoint=((a : ℂ) : OnePoint ℂ)) :
    (a : ℂ) ∈ closure (((↑) : ℍ → ℂ) '' R.val) := by
  have he : ((a : ℂ) : OnePoint ℂ) ∈ hTraceIdealEndpoints R.val := by
    rw [R.trace_idealEndpoint,ha]
    exact mem_singleton _
  exact ((hTraceIdealEndpoints_finite_iff R.val (a : ℂ)).mp he).1

theorem HRayAt.tangentSign_circle_left {p : ℍ} (R : HRayAt p) (c r : ℝ) (hr : 0<r)
    (hL : R.supportLine=HalfPlaneLine.circle c r hr)
    (ha : R.idealEndpoint=(((c-r : ℝ) : ℂ) : OnePoint ℂ)) : R.tangentSign=1 := by
  have hp := R.start_mem_support
  rw [hL] at hp
  have hpc := norm_sub_real_eq_radius_sq hp
  have hleft : c-r<p.re := by nlinarith [sq_pos_of_pos p.im_pos]
  have hdir : R.longitudinal p<R.longitudinal R.directionPoint := by
    by_contra hh
    have hsub : (((↑) : ℍ → ℂ) '' R.val) ⊆ {w : ℂ | p.re≤w.re} := by
      rintro _ ⟨w,hw,rfl⟩
      have he := (R.mem_iff_longitudinal (R.subset_support hw)).mp hw
      rw [ite_eq_right hh] at he
      change R.supportLine.longitudinal (w : ℂ)≤R.supportLine.longitudinal (p : ℂ) at he
      rw [hL] at he
      change -w.re≤-p.re at he
      change p.re≤w.re
      linarith
    have hc := closure_minimal hsub (isClosed_le continuous_const Complex.continuous_re)
      (R.re_mem_closure_of_idealEndpoint (c-r) ha)
    change p.re≤c-r at hc
    linarith
  exact ite_eq_left hdir

theorem HRayAt.tangentSign_circle_right {p : ℍ} (R : HRayAt p) (c r : ℝ) (hr : 0<r)
    (hL : R.supportLine=HalfPlaneLine.circle c r hr)
    (ha : R.idealEndpoint=(((c+r : ℝ) : ℂ) : OnePoint ℂ)) : R.tangentSign= -1 := by
  have hp := R.start_mem_support
  rw [hL] at hp
  have hpc := norm_sub_real_eq_radius_sq hp
  have hright : p.re<c+r := by nlinarith [sq_pos_of_pos p.im_pos]
  have hdir : ¬R.longitudinal p<R.longitudinal R.directionPoint := by
    intro hh
    have hsub : (((↑) : ℍ → ℂ) '' R.val) ⊆ {w : ℂ | w.re≤p.re} := by
      rintro _ ⟨w,hw,rfl⟩
      have he := (R.mem_iff_longitudinal (R.subset_support hw)).mp hw
      rw [ite_eq_left hh] at he
      change R.supportLine.longitudinal (p : ℂ)≤R.supportLine.longitudinal (w : ℂ) at he
      rw [hL] at he
      change -p.re≤-w.re at he
      change w.re≤p.re
      linarith
    have hc := closure_minimal hsub (isClosed_le Complex.continuous_re continuous_const)
      (R.re_mem_closure_of_idealEndpoint (c+r) ha)
    change c+r≤p.re at hc
    linarith
  exact ite_eq_right hdir

theorem HRayAt.tangentVector_circle_left {p : ℍ} (R : HRayAt p) (c r : ℝ) (hr : 0<r)
    (hL : R.supportLine=HalfPlaneLine.circle c r hr)
    (ha : R.idealEndpoint=(((c-r : ℝ) : ℂ) : OnePoint ℂ)) :
    R.tangentVector=Complex.I*((p : ℂ)-(c : ℂ)) := by
  rw [HRayAt.tangentVector,R.tangentSign_circle_left c r hr hL ha,hL,one_smul]
  rfl

theorem HRayAt.tangentVector_circle_right {p : ℍ} (R : HRayAt p) (c r : ℝ) (hr : 0<r)
    (hL : R.supportLine=HalfPlaneLine.circle c r hr)
    (ha : R.idealEndpoint=(((c+r : ℝ) : ℂ) : OnePoint ℂ)) :
    R.tangentVector= -(Complex.I*((p : ℂ)-(c : ℂ))) := by
  rw [HRayAt.tangentVector,R.tangentSign_circle_right c r hr hL ha,hL,neg_one_smul]
  rfl

theorem hInteriorAngleMeasure_infty_circle_left_cos {p : ℍ} (R S : HRayAt p)
    (c r : ℝ) (hr : 0<r) (hR : R.idealEndpoint=∞)
    (hL : S.supportLine=HalfPlaneLine.circle c r hr)
    (hS : S.idealEndpoint=(((c-r : ℝ) : ℂ) : OnePoint ℂ)) :
    Real.cos (hInteriorAngleMeasure R S)=(p.re-c)/r := by
  have hp := S.start_mem_support
  rw [hL] at hp
  change ‖(p : ℂ)-(c : ℂ)‖=r at hp
  have he := cos_angle_mul_norm_mul_norm R.tangentVector S.tangentVector
  rw [← hInteriorAngleMeasure,R.tangentVector_of_idealEndpoint_infty hR,
    S.tangentVector_circle_left c r hr hL hS,norm_mul,Complex.norm_I,one_mul,hp,
    _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates] at he
  simp only [Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,Complex.mul_im,
    Complex.sub_re,Complex.ofReal_re,UpperHalfPlane.coe_re,Complex.mul_re] at he
  exact (eq_div_iff hr.ne').mpr he

theorem hInteriorAngleMeasure_infty_circle_right_cos {p : ℍ} (R S : HRayAt p)
    (c r : ℝ) (hr : 0<r) (hR : R.idealEndpoint=∞)
    (hL : S.supportLine=HalfPlaneLine.circle c r hr)
    (hS : S.idealEndpoint=(((c+r : ℝ) : ℂ) : OnePoint ℂ)) :
    Real.cos (hInteriorAngleMeasure R S)=(c-p.re)/r := by
  have hp := S.start_mem_support
  rw [hL] at hp
  change ‖(p : ℂ)-(c : ℂ)‖=r at hp
  have he := cos_angle_mul_norm_mul_norm R.tangentVector S.tangentVector
  rw [← hInteriorAngleMeasure,R.tangentVector_of_idealEndpoint_infty hR,
    S.tangentVector_circle_right c r hr hL hS,norm_neg,norm_mul,Complex.norm_I,one_mul,hp,
    _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates] at he
  simp only [Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,Complex.neg_re,Complex.neg_im,
    Complex.mul_im,Complex.sub_re,Complex.ofReal_re,UpperHalfPlane.coe_re,Complex.mul_re] at he
  apply (eq_div_iff hr.ne').mpr
  linarith [he]


theorem infty_real_crossRatio_sin_half (b d θ : ℝ) (hbd : b≠d) (hd : d≠0)
    (hc : Real.cos θ=(b+d)/(b-d)) :
    Mobius.extendedCrossRatio ∞ ((b : ℂ) : OnePoint ℂ) ((0 : ℂ) : OnePoint ℂ)
      ((d : ℂ) : OnePoint ℂ)*((Real.sin (θ/2)^2 : ℝ) : ℂ)=1 := by
  have hh := Real.cos_two_mul_eq_one_sub (θ/2)
  rw [show 2*(θ/2)=θ by ring,hc] at hh
  have hs : Real.sin (θ/2)^2= -d/(b-d) := by
    apply (eq_div_iff (sub_ne_zero.mpr hbd)).mpr
    field_simp [sub_ne_zero.mpr hbd] at hh
    nlinarith only [hh]
  rw [hs,Mobius.extendedCrossRatio_infty_first]
  have he : (b-d)/(0-d)*(-d/(b-d))=1 := by
    field_simp [hd,sub_ne_zero.mpr hbd]
    ring
  exact_mod_cast he

theorem hRay_crossRatio_I_infty {p : ℍ} (R S : HRayAt p) (hp : p=UpperHalfPlane.I)
    (hR : R.idealEndpoint=∞) (c r : ℝ) (hr : 0<r)
    (hL : S.supportLine=HalfPlaneLine.circle c r hr)
    (d : OnePoint ℂ) (hd : d ∈ S.supportLine.idealEndpoints) (hdb : S.idealEndpoint≠d) :
    Mobius.extendedCrossRatio ∞ S.idealEndpoint ((0 : ℂ) : OnePoint ℂ) d*
      ((Real.sin (hInteriorAngleMeasure R S/2)^2 : ℝ) : ℂ)=1 := by
  have hpS := S.start_mem_support
  rw [hL] at hpS
  have hcoords := norm_sub_real_eq_radius_sq hpS
  rw [hp,UpperHalfPlane.I_re,UpperHalfPlane.I_im] at hcoords
  have hcp : c+r≠0 := by intro he; nlinarith
  have hcm : c-r≠0 := by intro he; nlinarith
  have hb := S.ideal_mem_support
  rw [hL,circle_idealEndpoints] at hb hd
  simp only [mem_insert_iff,mem_singleton_iff] at hb hd
  rcases hb with hb | hb
  · have hd' := hd.resolve_left (fun he => hdb (hb.trans he.symm))
    rw [hb,hd']
    apply infty_real_crossRatio_sin_half (c-r) (c+r) _ (by linarith) hcp
    have hc := hInteriorAngleMeasure_infty_circle_left_cos R S c r hr hR hL hb
    have hpRe : p.re=0 := by rw [hp]; rfl
    rw [hpRe,zero_sub] at hc
    rw [hc]
    rw [show c-r+(c+r)=2*c by ring,show c-r-(c+r)= -(2*r) by ring]
    field_simp [hr.ne']
  · have hd' := hd.resolve_right (fun he => hdb (hb.trans he.symm))
    rw [hb,hd']
    apply infty_real_crossRatio_sin_half (c+r) (c-r) _ (by linarith) hcm
    have hc := hInteriorAngleMeasure_infty_circle_right_cos R S c r hr hR hL hb
    have hpRe : p.re=0 := by rw [hp]; rfl
    rw [hpRe,sub_zero] at hc
    rw [hc]
    rw [show c+r+(c-r)=2*c by ring,show c+r-(c-r)=2*r by ring]
    field_simp [hr.ne']

/-- With the angle of the actual forward rays towards the first ideal ends. -/
theorem hRay_endpoint_crossRatio_angle {p : ℍ} (R S : HRayAt p)
    (hne : R.supportLine≠S.supportLine) (c d : OnePoint ℂ)
    (hc : c ∈ R.supportLine.idealEndpoints) (hca : R.idealEndpoint≠c)
    (hd : d ∈ S.supportLine.idealEndpoints) (hdb : S.idealEndpoint≠d) :
    Mobius.extendedCrossRatio R.idealEndpoint S.idealEndpoint c d*
      ((Real.sin (hInteriorAngleMeasure R S/2)^2 : ℝ) : ℂ)=1 := by
  obtain ⟨s,hp,hR⟩ := R.exists_sl2_normalized_upward
  let g := Matrix.SpecialLinearGroup.mapGL ℝ s
  have hg : 0<g.val.det := by simp [g]
  let R' := R.realGLMap g
  let S' := S.realGLMap g
  have hR' : R'.idealEndpoint=∞ := hR
  have hp' : g • p=UpperHalfPlane.I := hp
  have hRL : R'.supportLine=HalfPlaneLine.vertical 0 := by
    rw [R'.supportLine_of_idealEndpoint_infty hR']
    change HalfPlaneLine.vertical (g • p).re=HalfPlaneLine.vertical 0
    rw [hp']
    rfl
  have hne' : R'.supportLine≠S'.supportLine := by
    intro he
    apply hne
    apply HalfPlaneLine.carrier_injective
    apply (realGL_isometry g).injective.image_injective
    rw [R.realGLMap_support,S.realGLMap_support]
    exact congrArg HalfPlaneLine.carrier he
  have hC : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) c ∈ R'.supportLine.idealEndpoints := by
    rw [R.supportLine.idealEndpoints_realGL_image R'.supportLine g hg (R.realGLMap_support g)]
    exact mem_image_of_mem _ hc
  have hD : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) d ∈ S'.supportLine.idealEndpoints := by
    rw [S.supportLine.idealEndpoints_realGL_image S'.supportLine g hg (S.realGLMap_support g)]
    exact mem_image_of_mem _ hd
  have hC0 : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) c=((0 : ℂ) : OnePoint ℂ) := by
    rw [hRL,vertical_idealEndpoints] at hC
    simp only [Complex.ofReal_zero,mem_insert_iff,mem_singleton_iff] at hC
    apply hC.resolve_right
    intro he
    apply hca
    apply (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)).injective
    rw [← R.realGLMap_idealEndpoint g hg,hR',he]
  have hDS : S'.idealEndpoint≠Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) d := by
    rw [S.realGLMap_idealEndpoint g hg]
    exact (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)).injective.ne hdb
  have hAng := hInteriorAngleMeasure_realGLMap R S g
  have hRatio := Mobius.extendedCrossRatio_fractionalLinear (complexifiedRealMobiusMatrix g)
    R.idealEndpoint S.idealEndpoint c d
  rw [← R.realGLMap_idealEndpoint g hg,← S.realGLMap_idealEndpoint g hg,hR',hC0] at hRatio
  have hGoal : Mobius.extendedCrossRatio ∞ S'.idealEndpoint ((0 : ℂ) : OnePoint ℂ)
      (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) d)*
      ((Real.sin (hInteriorAngleMeasure R' S'/2)^2 : ℝ) : ℂ)=1 := by
    cases hSL : S'.supportLine with
    | vertical x =>
      have hpS := S'.start_mem_support
      rw [hSL] at hpS
      change (g • p).re=x at hpS
      rw [hp'] at hpS
      have hx : x=0 := hpS.symm
      exact (hne' (hRL.trans (by rw [hSL,hx]))).elim
    | circle a r hr =>
      exact hRay_crossRatio_I_infty R' S' hp' hR' a r hr hSL _ hD hDS
  rwa [hRatio,hAng] at hGoal


theorem discRay_endpoint_crossRatio_angle {p : 𝔻} (R S : DiscRayAt p)
    (hne : R.supportLine≠S.supportLine) (c d : OnePoint ℂ)
    (hc : c ∈ R.supportLine.idealEndpoints) (hca : R.idealEndpoint≠c)
    (hd : d ∈ S.supportLine.idealEndpoints) (hdb : S.idealEndpoint≠d) :
    Mobius.extendedCrossRatio R.idealEndpoint S.idealEndpoint c d*
      ((Real.sin (discInteriorAngleMeasure R S/2)^2 : ℝ) : ℂ)=1 := by
  have hmem (K : DiscLine) (u : OnePoint ℂ) (hu : u ∈ K.idealEndpoints) :
      extendedCayley.symm u ∈ K.toHalfPlane.idealEndpoints := by
    rw [K.idealEndpoints_eq_cayley_image] at hu
    obtain ⟨x,hx,rfl⟩ := hu
    simpa only [Homeomorph.symm_apply_apply] using hx
  have hcH : extendedCayley.symm c ∈ R.toHalfPlane.supportLine.idealEndpoints := by
    have he := hmem R.supportLine c hc
    change extendedCayley.symm c ∈ R.toHalfPlane.supportLine.toDiscLine.toHalfPlane.idealEndpoints at he
    rwa [HalfPlaneLine.toDiscLine_toHalfPlane] at he
  have hdH : extendedCayley.symm d ∈ S.toHalfPlane.supportLine.idealEndpoints := by
    have he := hmem S.supportLine d hd
    change extendedCayley.symm d ∈ S.toHalfPlane.supportLine.toDiscLine.toHalfPlane.idealEndpoints at he
    rwa [HalfPlaneLine.toDiscLine_toHalfPlane] at he
  have hcaH : R.toHalfPlane.idealEndpoint≠extendedCayley.symm c := by
    rw [R.toHalfPlane_idealEndpoint]
    exact extendedCayley.symm.injective.ne hca
  have hdbH : S.toHalfPlane.idealEndpoint≠extendedCayley.symm d := by
    rw [S.toHalfPlane_idealEndpoint]
    exact extendedCayley.symm.injective.ne hdb
  have he := hRay_endpoint_crossRatio_angle R.toHalfPlane S.toHalfPlane
    ((R.different_supports_iff S).mp hne) _ _ hcH hcaH hdH hdbH
  rwa [R.toHalfPlane_idealEndpoint,S.toHalfPlane_idealEndpoint,
    extendedCrossRatio_inverseCayley,← discInteriorAngleMeasure_eq_halfPlane] at he

theorem hRay_endpoint_crossRatio_angle_statement {p : ℍ} (R S : HRayAt p)
    (hne : R.supportLine≠S.supportLine) (c d : OnePoint ℂ)
    (hc : c ∈ R.supportLine.idealEndpoints) (hca : R.idealEndpoint≠c)
    (hd : d ∈ S.supportLine.idealEndpoints) (hdb : S.idealEndpoint≠d) :
    hInteriorAngleMeasure R S ∈ Ioo (0 : ℝ) Real.pi ∧
      Mobius.extendedCrossRatio R.idealEndpoint S.idealEndpoint c d*
        ((Real.sin (hInteriorAngleMeasure R S/2)^2 : ℝ) : ℂ)=1 :=
  ⟨⟨hInteriorAngleMeasure_pos R S hne,hInteriorAngleMeasure_lt_pi R S hne⟩,
    hRay_endpoint_crossRatio_angle R S hne c d hc hca hd hdb⟩

theorem discRay_endpoint_crossRatio_angle_statement {p : 𝔻} (R S : DiscRayAt p)
    (hne : R.supportLine≠S.supportLine) (c d : OnePoint ℂ)
    (hc : c ∈ R.supportLine.idealEndpoints) (hca : R.idealEndpoint≠c)
    (hd : d ∈ S.supportLine.idealEndpoints) (hdb : S.idealEndpoint≠d) :
    discInteriorAngleMeasure R S ∈ Ioo (0 : ℝ) Real.pi ∧
      Mobius.extendedCrossRatio R.idealEndpoint S.idealEndpoint c d*
        ((Real.sin (discInteriorAngleMeasure R S/2)^2 : ℝ) : ℂ)=1 := by
  refine ⟨?_,discRay_endpoint_crossRatio_angle R S hne c d hc hca hd hdb⟩
  rw [discInteriorAngleMeasure_eq_halfPlane]
  exact ⟨hInteriorAngleMeasure_pos R.toHalfPlane S.toHalfPlane ((R.different_supports_iff S).mp hne),
    hInteriorAngleMeasure_lt_pi R.toHalfPlane S.toHalfPlane ((R.different_supports_iff S).mp hne)⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
