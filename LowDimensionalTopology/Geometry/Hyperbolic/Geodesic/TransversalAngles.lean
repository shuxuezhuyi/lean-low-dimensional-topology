/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.AngleCrossRatios
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.LineBisectors

/-!
# Genuine acute tangent angles and equal-angle transversals
-/
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- The smaller unoriented angle of the two actual tangent lines. -/
def acuteTangentAngle (u v : ℂ) : ℝ :=
  min (angle u v) (Real.pi-angle u v)

theorem acuteTangentAngle_comm (u v : ℂ) : acuteTangentAngle u v=acuteTangentAngle v u := by
  simp only [acuteTangentAngle,angle_comm u v]

theorem acuteTangentAngle_neg_left (u v : ℂ) :
    acuteTangentAngle (-u) v=acuteTangentAngle u v := by
  simp only [acuteTangentAngle,angle_neg_left,sub_sub_cancel,min_comm]

theorem acuteTangentAngle_neg_right (u v : ℂ) :
    acuteTangentAngle u (-v)=acuteTangentAngle u v := by
  rw [acuteTangentAngle_comm,acuteTangentAngle_neg_left,acuteTangentAngle_comm]

theorem acuteTangentAngle_smul_left (u v : ℂ) (r : ℝ) (hr : r≠0) :
    acuteTangentAngle (r • u) v=acuteTangentAngle u v := by
  rcases hr.lt_or_gt with hr | hr
  · change min (angle (r • u) v) (Real.pi-angle (r • u) v)=_
    rw [angle_smul_left_of_neg _ _ hr]
    exact acuteTangentAngle_neg_left u v
  · simp only [acuteTangentAngle,angle_smul_left_of_pos _ _ hr]

theorem acuteTangentAngle_smul_right (u v : ℂ) (r : ℝ) (hr : r≠0) :
    acuteTangentAngle u (r • v)=acuteTangentAngle u v := by
  rw [acuteTangentAngle_comm,acuteTangentAngle_smul_left _ _ r hr,acuteTangentAngle_comm]

theorem acuteTangentAngle_mem_Icc (u v : ℂ) :
    acuteTangentAngle u v ∈ Icc (0 : ℝ) (Real.pi/2) := by
  have h0:=angle_nonneg u v
  have hp:=angle_le_pi u v
  constructor
  · exact le_min h0 (sub_nonneg.mpr hp)
  · by_cases hh : angle u v≤Real.pi/2
    · exact (min_le_left _ _).trans hh
    · exact (min_le_right _ _).trans (by linarith)

theorem acuteTangentAngle_cos_abs (u v : ℂ) :
    Real.cos (acuteTangentAngle u v)=|Real.cos (angle u v)| := by
  have h0:=angle_nonneg u v
  have hp:=angle_le_pi u v
  by_cases hh : angle u v≤Real.pi/2
  · rw [acuteTangentAngle,min_eq_left (by linarith),abs_of_nonneg]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hh⟩
  · rw [acuteTangentAngle,min_eq_right (by linarith),Real.cos_pi_sub,abs_of_nonpos]
    exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [Real.pi_pos])

theorem acuteTangentAngle_cos (u v : ℂ) :
    Real.cos (acuteTangentAngle u v)=|inner ℝ u v|/(‖u‖*‖v‖) := by
  rw [acuteTangentAngle_cos_abs,cos_angle,abs_div,abs_mul,abs_norm,abs_norm]

theorem acuteTangentAngle_eq_pi_half_iff (u v : ℂ) :
    acuteTangentAngle u v=Real.pi/2 ↔ inner ℝ u v=0 := by
  have ha:=acuteTangentAngle_mem_Icc u v
  constructor
  · intro h
    have he:=acuteTangentAngle_cos u v
    rw [h,Real.cos_pi_div_two] at he
    have he0 := (div_eq_zero_iff).mp he.symm
    rcases he0 with he0 | he0
    · exact abs_eq_zero.mp he0
    · rcases mul_eq_zero.mp he0 with hu | hv
      · simp only [norm_eq_zero] at hu
        simp [hu]
      · simp only [norm_eq_zero] at hv
        simp [hv]
  · intro h
    apply Real.injOn_cos ⟨ha.1,by linarith [ha.2,Real.pi_pos]⟩
      ⟨by positivity,by linarith [Real.pi_pos]⟩
    rw [acuteTangentAngle_cos,h,abs_zero,zero_div,Real.cos_pi_div_two]

def HalfPlaneLine.acuteAngle (L M : HalfPlaneLine) (p : ℍ) : ℝ :=
  acuteTangentAngle (L.tangentAt p) (M.tangentAt p)

theorem HalfPlaneLine.acuteAngle_comm (L M : HalfPlaneLine) (p : ℍ) :
    L.acuteAngle M p=M.acuteAngle L p := acuteTangentAngle_comm _ _

theorem HalfPlaneLine.acuteAngle_mem_Icc (L M : HalfPlaneLine) (p : ℍ) :
    L.acuteAngle M p ∈ Icc (0 : ℝ) (Real.pi/2) := acuteTangentAngle_mem_Icc _ _

theorem HalfPlaneLine.acuteAngle_eq_pi_half_iff (L M : HalfPlaneLine) (p : ℍ)
    (hpL : p∈L.carrier) (hpM : p∈M.carrier) :
    L.acuteAngle M p=Real.pi/2 ↔ L.OrthogonalAt M p := by
  rw [HalfPlaneLine.acuteAngle,acuteTangentAngle_eq_pi_half_iff]
  exact ⟨fun h=>⟨hpL,hpM,h⟩,fun h=>h.2.2⟩

theorem HRayAt.acuteAngle_eq_support {p : ℍ} (R S : HRayAt p) :
    min (hInteriorAngleMeasure R S) (Real.pi-hInteriorAngleMeasure R S)=
      R.supportLine.acuteAngle S.supportLine p := by
  change acuteTangentAngle R.tangentVector S.tangentVector=_
  rw [HRayAt.tangentVector,HRayAt.tangentVector,
    acuteTangentAngle_smul_left _ _ _ R.tangentSign_ne_zero,
    acuteTangentAngle_smul_right _ _ _ S.tangentSign_ne_zero]
  rfl

theorem HalfPlaneLine.exists_rayAt (L : HalfPlaneLine) (p : ℍ) (hp : p∈L.carrier) :
    ∃R : HRayAt p,R.supportLine=L := by
  obtain ⟨a,b,γ,hab,ha,hb,he,hrest⟩:=L.exists_idealEndpoints_pair
  let R:=HRayAt.canonical p a ha
  have hR : R.idealEndpoint=a:=R.idealEndpoint_unique (isHLineRay_hRay p a ha)
  refine ⟨R,R.supportLine.eq_of_shared_ideal_and_interior L p R.start_mem_support hp a ?_ ?_⟩
  · rw [←hR]
    exact R.ideal_mem_support
  · rw [he]
    exact mem_insert _ _

def HalfPlaneLine.rayAt (L : HalfPlaneLine) (p : ℍ) (hp : p∈L.carrier) : HRayAt p :=
  (L.exists_rayAt p hp).choose

theorem HalfPlaneLine.rayAt_support (L : HalfPlaneLine) (p : ℍ) (hp : p∈L.carrier) :
    (L.rayAt p hp).supportLine=L := (L.exists_rayAt p hp).choose_spec

theorem HalfPlaneLine.acuteAngle_realGL_image (L M L' M' : HalfPlaneLine)
    (g : GL (Fin 2) ℝ) (hL : (g • · : ℍ→ℍ) '' L.carrier=L'.carrier)
    (hM : (g • · : ℍ→ℍ) '' M.carrier=M'.carrier) (p : ℍ)
    (hpL : p∈L.carrier) (hpM : p∈M.carrier) :
    L'.acuteAngle M' (g • p)=L.acuteAngle M p := by
  let R:=L.rayAt p hpL
  let S:=M.rayAt p hpM
  have hR : (R.realGLMap g).supportLine=L' := by
    apply HalfPlaneLine.carrier_injective
    rw [←R.realGLMap_support,show R.supportLine=L from L.rayAt_support p hpL]
    exact hL
  have hS : (S.realGLMap g).supportLine=M' := by
    apply HalfPlaneLine.carrier_injective
    rw [←S.realGLMap_support,show S.supportLine=M from M.rayAt_support p hpM]
    exact hM
  have he:=(R.realGLMap g).acuteAngle_eq_support (S.realGLMap g)
  rw [hR,hS,hInteriorAngleMeasure_realGLMap] at he
  rw [←he,R.acuteAngle_eq_support S]
  rw [show R.supportLine=L from L.rayAt_support p hpL,
    show S.supportLine=M from M.rayAt_support p hpM]

def DiscLine.rayAt (L : DiscLine) (p : 𝔻) (hp : p∈L.carrier) : DiscRayAt p :=
  (L.toHalfPlane.rayAt (discToHalfPlane p) ((L.mem_carrier p).mp hp)).toDiscAt p

theorem DiscLine.rayAt_toHalfPlane (L : DiscLine) (p : 𝔻) (hp : p∈L.carrier) :
    (L.rayAt p hp).toHalfPlane=
      L.toHalfPlane.rayAt (discToHalfPlane p) ((L.mem_carrier p).mp hp) :=
  (discRayHalfPlaneEquiv p).right_inv _

theorem DiscLine.rayAt_support (L : DiscLine) (p : 𝔻) (hp : p∈L.carrier) :
    (L.rayAt p hp).supportLine=L := by
  rw [DiscRayAt.supportLine,L.rayAt_toHalfPlane,HalfPlaneLine.rayAt_support,L.toHalfPlane_spec]

/-- This uses actual Euclidean disc ray tangents, not a definition by pullback. -/
def DiscLine.acuteAngle (L M : DiscLine) (p : 𝔻) (hpL : p∈L.carrier) (hpM : p∈M.carrier) : ℝ :=
  min (discInteriorAngleMeasure (L.rayAt p hpL) (M.rayAt p hpM))
    (Real.pi-discInteriorAngleMeasure (L.rayAt p hpL) (M.rayAt p hpM))

theorem DiscLine.acuteAngle_eq_halfPlane (L M : DiscLine) (p : 𝔻)
    (hpL : p∈L.carrier) (hpM : p∈M.carrier) :
    L.acuteAngle M p hpL hpM=L.toHalfPlane.acuteAngle M.toHalfPlane (discToHalfPlane p) := by
  rw [DiscLine.acuteAngle,discInteriorAngleMeasure_eq_halfPlane,HRayAt.acuteAngle_eq_support,
    L.rayAt_toHalfPlane,M.rayAt_toHalfPlane,HalfPlaneLine.rayAt_support,HalfPlaneLine.rayAt_support]

theorem DiscLine.acuteAngle_eq_pi_half_iff (L M : DiscLine) (p : 𝔻)
    (hpL : p∈L.carrier) (hpM : p∈M.carrier) :
    L.acuteAngle M p hpL hpM=Real.pi/2 ↔ L.OrthogonalAt M p := by
  rw [L.acuteAngle_eq_halfPlane M p hpL hpM,L.orthogonalAt_iff_halfPlane]
  exact L.toHalfPlane.acuteAngle_eq_pi_half_iff M.toHalfPlane _
    ((L.mem_carrier p).mp hpL) ((M.mem_carrier p).mp hpM)

/-- A genuine geodesic meeting both given lines at the specified acute angle. -/
def HalfPlaneLine.IsThetaTransversal (L M : HalfPlaneLine) (θ : ℝ) (N : HalfPlaneLine) : Prop :=
  0<θ ∧ θ≤Real.pi/2 ∧ ∃p q : ℍ,p∈L.carrier ∧ p∈N.carrier ∧ q∈M.carrier ∧ q∈N.carrier ∧
    L.acuteAngle N p=θ ∧ M.acuteAngle N q=θ

def DiscLine.IsThetaTransversal (L M : DiscLine) (θ : ℝ) (N : DiscLine) : Prop :=
  0<θ ∧ θ≤Real.pi/2 ∧ ∃(p q : 𝔻) (hpL : p∈L.carrier) (hpN : p∈N.carrier)
    (hqM : q∈M.carrier) (hqN : q∈N.carrier),
    L.acuteAngle N p hpL hpN=θ ∧ M.acuteAngle N q hqM hqN=θ

theorem HalfPlaneLine.isThetaTransversal_pi_half_iff (L M N : HalfPlaneLine) :
    L.IsThetaTransversal M (Real.pi/2) N ↔ L.Orthogonal N ∧ M.Orthogonal N := by
  constructor
  · rintro ⟨_,_,p,q,hpL,hpN,hqM,hqN,hp,hq⟩
    exact ⟨⟨p,(L.acuteAngle_eq_pi_half_iff N p hpL hpN).mp hp⟩,
      ⟨q,(M.acuteAngle_eq_pi_half_iff N q hqM hqN).mp hq⟩⟩
  · rintro ⟨⟨p,hpL,hpN,hp⟩,⟨q,hqM,hqN,hq⟩⟩
    exact ⟨by positivity,le_rfl,p,q,hpL,hpN,hqM,hqN,
      (L.acuteAngle_eq_pi_half_iff N p hpL hpN).mpr ⟨hpL,hpN,hp⟩,
      (M.acuteAngle_eq_pi_half_iff N q hqM hqN).mpr ⟨hqM,hqN,hq⟩⟩

theorem HalfPlaneLine.existsUnique_pi_half_transversal (L M : HalfPlaneLine) (hd : L.HDisjoint M) :
    ∃!N,L.IsThetaTransversal M (Real.pi/2) N := by
  simpa only [HalfPlaneLine.isThetaTransversal_pi_half_iff] using L.existsUnique_commonOrthogonal M hd

theorem DiscLine.isThetaTransversal_iff_halfPlane (L M N : DiscLine) (θ : ℝ) :
    L.IsThetaTransversal M θ N ↔ L.toHalfPlane.IsThetaTransversal M.toHalfPlane θ N.toHalfPlane := by
  constructor
  · rintro ⟨h0,hθ,p,q,hpL,hpN,hqM,hqN,hp,hq⟩
    refine ⟨h0,hθ,discToHalfPlane p,discToHalfPlane q,(L.mem_carrier p).mp hpL,
      (N.mem_carrier p).mp hpN,(M.mem_carrier q).mp hqM,(N.mem_carrier q).mp hqN,?_,?_⟩
    · exact (L.acuteAngle_eq_halfPlane N p hpL hpN).symm.trans hp
    · exact (M.acuteAngle_eq_halfPlane N q hqM hqN).symm.trans hq
  · rintro ⟨h0,hθ,p,q,hpL,hpN,hqM,hqN,hp,hq⟩
    have hpL' : halfPlaneToDisc p∈L.carrier :=
      (L.mem_carrier _).mpr (by simpa only [discToHalfPlane_halfPlaneToDisc] using hpL)
    have hpN' : halfPlaneToDisc p∈N.carrier :=
      (N.mem_carrier _).mpr (by simpa only [discToHalfPlane_halfPlaneToDisc] using hpN)
    have hqM' : halfPlaneToDisc q∈M.carrier :=
      (M.mem_carrier _).mpr (by simpa only [discToHalfPlane_halfPlaneToDisc] using hqM)
    have hqN' : halfPlaneToDisc q∈N.carrier :=
      (N.mem_carrier _).mpr (by simpa only [discToHalfPlane_halfPlaneToDisc] using hqN)
    refine ⟨h0,hθ,halfPlaneToDisc p,halfPlaneToDisc q,hpL',hpN',hqM',hqN',?_,?_⟩
    · simpa only [L.acuteAngle_eq_halfPlane,discToHalfPlane_halfPlaneToDisc] using hp
    · simpa only [M.acuteAngle_eq_halfPlane,discToHalfPlane_halfPlaneToDisc] using hq

theorem DiscLine.existsUnique_pi_half_transversal (L M : DiscLine) (hd : L.HDisjoint M) :
    ∃!N,L.IsThetaTransversal M (Real.pi/2) N := by
  obtain ⟨N,hN,hu⟩:=L.existsUnique_commonOrthogonal M hd
  have he (P : DiscLine) : L.IsThetaTransversal M (Real.pi/2) P ↔
      L.Orthogonal P ∧ M.Orthogonal P := by
    rw [L.isThetaTransversal_iff_halfPlane M P,
      HalfPlaneLine.isThetaTransversal_pi_half_iff,L.orthogonal_iff_halfPlane P,
      M.orthogonal_iff_halfPlane P]
  exact ⟨N,(he N).mpr hN,fun P hP=>hu P ((he P).mp hP)⟩


theorem HalfPlaneLine.acuteAngle_pos (L M : HalfPlaneLine) (p : ℍ)
    (hpL : p∈L.carrier) (hpM : p∈M.carrier) (hne : L≠M) : 0<L.acuteAngle M p := by
  let R:=L.rayAt p hpL
  let S:=M.rayAt p hpM
  have hRS : R.supportLine≠S.supportLine := by
    rw [show R.supportLine=L from L.rayAt_support p hpL,
      show S.supportLine=M from M.rayAt_support p hpM]
    exact hne
  have hR : R.supportLine=L:=L.rayAt_support p hpL
  have hS : S.supportLine=M:=M.rayAt_support p hpM
  rw [←hR,←hS,←R.acuteAngle_eq_support S]
  exact lt_min (hInteriorAngleMeasure_pos R S hRS)
    (sub_pos.mpr (hInteriorAngleMeasure_lt_pi R S hRS))

theorem vertical_circle_acuteAngle_cos (a c r : ℝ) (hr : 0<r) (p : ℍ)
    (hp : p∈(HalfPlaneLine.circle c r hr).carrier) :
    Real.cos ((HalfPlaneLine.vertical a).acuteAngle (.circle c r hr) p)=|p.re-c|/r := by
  change Real.cos (acuteTangentAngle Complex.I (Complex.I*((p : ℂ)-(c : ℂ))))=_
  rw [acuteTangentAngle_cos,norm_mul,Complex.norm_I,one_mul,one_mul,hp]
  have he : inner ℝ Complex.I (Complex.I*((p : ℂ)-(c : ℂ)))=p.re-c := by
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    simp only [Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,Complex.mul_im,
      Complex.sub_re,Complex.ofReal_re,UpperHalfPlane.coe_re]
  rw [he]

theorem circle_circle_acuteAngle_cos (c r d s : ℝ) (hr : 0<r) (hs : 0<s) (p : ℍ)
    (hp : p∈(HalfPlaneLine.circle c r hr).carrier)
    (hq : p∈(HalfPlaneLine.circle d s hs).carrier) :
    Real.cos ((HalfPlaneLine.circle c r hr).acuteAngle (.circle d s hs) p)=
      |r^2+s^2-(c-d)^2|/(2*r*s) := by
  have hp2:=norm_sub_real_eq_radius_sq hp
  have hq2:=norm_sub_real_eq_radius_sq hq
  have he : inner ℝ ((p : ℂ)-(c : ℂ)) ((p : ℂ)-(d : ℂ))=
      (r^2+s^2-(c-d)^2)/2 := by
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero,
      UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
    nlinarith only [hp2,hq2]
  change Real.cos (acuteTangentAngle (Complex.I*((p : ℂ)-(c : ℂ)))
    (Complex.I*((p : ℂ)-(d : ℂ))))=_
  rw [acuteTangentAngle_cos,complex_real_inner_mul_I,norm_mul,norm_mul,
    Complex.norm_I,one_mul,one_mul,hp,hq,he,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  ring

theorem HalfPlaneLine.isThetaTransversal_realGL_image_iff (L M N L' M' N' : HalfPlaneLine)
    (g : GL (Fin 2) ℝ) (hL : (g • · : ℍ→ℍ) '' L.carrier=L'.carrier)
    (hM : (g • · : ℍ→ℍ) '' M.carrier=M'.carrier)
    (hN : (g • · : ℍ→ℍ) '' N.carrier=N'.carrier) (θ : ℝ) :
    L'.IsThetaTransversal M' θ N' ↔ L.IsThetaTransversal M θ N := by
  constructor
  · rintro ⟨h0,hθ,p,q,hpL,hpN,hqM,hqN,hp,hq⟩
    obtain ⟨p',hpL',rfl⟩:=hL ▸ hpL
    obtain ⟨q',hqM',rfl⟩:=hM ▸ hqM
    have hpN' : p'∈N.carrier := by
      have hh : g • p'∈(g • · : ℍ→ℍ) '' N.carrier:=hN ▸ hpN
      obtain ⟨x,hx,he⟩:=hh
      exact (realGL_isometry g).injective he ▸ hx
    have hqN' : q'∈N.carrier := by
      have hh : g • q'∈(g • · : ℍ→ℍ) '' N.carrier:=hN ▸ hqN
      obtain ⟨x,hx,he⟩:=hh
      exact (realGL_isometry g).injective he ▸ hx
    refine ⟨h0,hθ,p',q',hpL',hpN',hqM',hqN',?_,?_⟩
    · exact (L.acuteAngle_realGL_image N L' N' g hL hN p' hpL' hpN').symm.trans hp
    · exact (M.acuteAngle_realGL_image N M' N' g hM hN q' hqM' hqN').symm.trans hq
  · rintro ⟨h0,hθ,p,q,hpL,hpN,hqM,hqN,hp,hq⟩
    refine ⟨h0,hθ,g • p,g • q,hL ▸ mem_image_of_mem _ hpL,
      hN ▸ mem_image_of_mem _ hpN,hM ▸ mem_image_of_mem _ hqM,hN ▸ mem_image_of_mem _ hqN,?_,?_⟩
    · exact (L.acuteAngle_realGL_image N L' N' g hL hN p hpL hpN).trans hp
    · exact (M.acuteAngle_realGL_image N M' N' g hM hN q hqM hqN).trans hq

end
end LowDimensionalTopology.Geometry.Hyperbolic
