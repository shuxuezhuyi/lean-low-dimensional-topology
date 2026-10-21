/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.NativeParabolicPencils
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Inversive
noncomputable section

/-- The actual hyperbolic metric sphere, allowing a separate degenerate zero-radius sphere. -/
def hMetricCircle (p : ℍ) (r : ℝ) : Set ℍ := {z | dist z p=r}

/-- The regular complementary curves have strictly positive radius. -/
def hMetricCircleFamily (p : ℍ) : Set (Set ℍ) := {S | ∃r : ℝ,0<r ∧ S=hMetricCircle p r}

def hEllipticPencil (p : ℍ) : Set HalfPlaneLine := {L | p∈L.carrier}

theorem hMetricCircle_zero (p : ℍ) : hMetricCircle p 0={p} := by
  ext z
  exact dist_eq_zero

theorem hMetricCircle_nonempty (p : ℍ) (r : ℝ) (hr : 0≤r) : (hMetricCircle p r).Nonempty := by
  let L:=HalfPlaneLine.vertical p.re
  obtain ⟨γ,hγ,hrange⟩:=L.exists_isometric_param
  have hp : p∈range γ:=hrange ▸ (show p∈L.carrier from rfl)
  obtain ⟨s,hs⟩:=hp
  refine ⟨γ (s+r),?_⟩
  change dist (γ (s+r)) p=r
  rw [←hs,hγ.dist_eq,Real.dist_eq]
  have he : s+r-s=r:=by ring
  rw [he,abs_of_nonneg hr]

/-- Corrected P1 for regular circles excludes the actual common center. -/
theorem existsUnique_hMetricCircle_through {p z : ℍ} (hz : z≠p) :
    ∃!S : Set ℍ,S∈hMetricCircleFamily p ∧ z∈S := by
  refine ⟨hMetricCircle p (dist z p),⟨⟨dist z p,dist_pos.mpr hz,rfl⟩,rfl⟩,?_⟩
  rintro S ⟨⟨r,hr,rfl⟩,hm⟩
  change dist z p=r at hm
  rw [hm]

/-- The literal unqualified regular-curve P1 fails at the actual elliptic center. -/
theorem center_not_mem_hMetricCircleFamily (p : ℍ) :
    ¬∃S∈hMetricCircleFamily p,p∈S := by
  rintro ⟨S,⟨r,hr,rfl⟩,hp⟩
  change dist p p=r at hp
  rw [dist_self] at hp
  linarith

theorem existsUnique_hEllipticPencil_through {p z : ℍ} (hz : z≠p) :
    ∃!L : HalfPlaneLine,L∈hEllipticPencil p ∧ z∈L.carrier := by
  exact existsUnique_halfPlaneLine_through p z hz.symm

theorem same_hMetricCircle_iff {p a b : ℍ} (hab : a≠b) :
    (∃S∈hMetricCircleFamily p,a∈S ∧ b∈S) ↔ dist a p=dist b p := by
  constructor
  · rintro ⟨S,⟨r,hr,rfl⟩,ha,hb⟩
    exact ha.trans hb.symm
  · intro he
    have hp : a≠p := by
      intro ha
      subst a
      have hb : b=p:=dist_eq_zero.mp (by simpa only [dist_self] using he.symm)
      exact hab hb.symm
    exact ⟨hMetricCircle p (dist a p),⟨_,dist_pos.mpr hp,rfl⟩,rfl,he.symm⟩

/-- P4 is invariance under the genuine reflection fixing the actual center. -/
theorem hMetricCircle_reflection (p : ℍ) (r : ℝ) (L : HalfPlaneLine) (hL : L∈hEllipticPencil p) :
    L.reflection '' hMetricCircle p r=hMetricCircle p r := by
  have hfix : L.reflection p=p:=(L.reflection_fixed_iff p).mpr hL
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    change dist (L.reflection w) p=r
    rw [←hfix,L.reflection_isometry.dist_eq]
    exact hw
  · intro hz
    refine ⟨L.reflection z,?_,L.reflection_involutive z⟩
    change dist (L.reflection z) p=r
    rw [←hfix,L.reflection_isometry.dist_eq]
    exact hz

/-- P6 uses the genuine geometric perpendicular bisector. -/
theorem hEllipticPencil_perpendicularBisector_iff (p : ℍ) {a b : ℍ} (hab : a≠b)
    {N : HalfPlaneLine} (hN : IsHPerpendicularBisector N a b) :
    N∈hEllipticPencil p ↔ ∃S∈hMetricCircleFamily p,a∈S ∧ b∈S := by
  rw [same_hMetricCircle_iff hab]
  change p∈N.carrier ↔ dist a p=dist b p
  rw [hN.carrier_eq hab]
  change dist p a=dist p b ↔ dist a p=dist b p
  rw [dist_comm p a,dist_comm p b]

theorem metricCircle_I_euclidean (r : ℝ) (hr : 0<r) (z : ℍ) :
    z∈hMetricCircle UpperHalfPlane.I r ↔
      ‖(z : ℂ)-(Real.cosh r : ℂ)*Complex.I‖=Real.sinh r := by
  have hs : 0<Real.sinh r:=Real.sinh_pos_iff.mpr hr
  have hc : dist z UpperHalfPlane.I=r ↔ Real.cosh (dist z UpperHalfPlane.I)=Real.cosh r :=
    ⟨congrArg Real.cosh,Real.cosh_injOn dist_nonneg hr.le⟩
  change dist z UpperHalfPlane.I=r ↔ _
  rw [hc,UpperHalfPlane.cosh_dist']
  change ((z.re-0)^2+z.im^2+1^2)/(2*z.im*1)=Real.cosh r ↔ _
  have hn : ‖(z : ℂ)-(Real.cosh r : ℂ)*Complex.I‖^2=z.re^2+(z.im-Real.cosh r)^2 := by
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero,
      UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
    ring
  rw [←sq_eq_sq₀ (norm_nonneg _) hs.le,hn]
  have hden : 2*z.im*1≠0:=by positivity
  rw [div_eq_iff hden]
  constructor <;> intro h <;> nlinarith [Real.cosh_sq_sub_sinh_sq r]

def metricCircleAtI (r : ℝ) (hr : 0<r) : Mobius.ComplexGeneralizedCircle :=
  ⟨Mobius.complexCircle ((Real.cosh r : ℂ)*Complex.I) (Real.sinh r),
    Mobius.complexCircle_isGeneralized _ _ (Real.sinh_pos_iff.mpr hr)⟩

theorem hMetricCircle_I_eq_circleCarrier (r : ℝ) (hr : 0<r) :
    hMetricCircle UpperHalfPlane.I r=halfPlaneCircleCarrier (metricCircleAtI r hr) := by
  ext z
  change z∈hMetricCircle UpperHalfPlane.I r ↔
    ((z : ℂ) : OnePoint ℂ)∈Mobius.complexCircle ((Real.cosh r : ℂ)*Complex.I) (Real.sinh r)
  rw [Mobius.complexCircle_coe]
  exact metricCircle_I_euclidean r hr z


theorem metricCircleAtI_orthogonal (r : ℝ) (hr : 0<r) (L : HalfPlaneLine)
    (hL : UpperHalfPlane.I∈L.carrier) : Mobius.ComplexCirclesOrthogonal L.extendedCircle (metricCircleAtI r hr) := by
  rw [Mobius.complexCirclesOrthogonal_iff_inversiveProduct_zero]
  cases L with
  | vertical a =>
    change (0 : ℝ)=a at hL
    subst a
    rw [HalfPlaneLine.extendedCircle,metricCircleAtI,complexLine_realModel 1 0 one_ne_zero,
      complexCircle_realModel _ _ (Real.sinh_pos_iff.mpr
        hr),Inversive.inversiveProduct_comm,Inversive.inversiveProduct_sphere_plane]
    simp [Mobius.complexPlaneCoordinates.inner_map_map]
  | circle c R hR =>
    have hc:=norm_sub_real_eq_radius_sq hL
    change (0-c)^2+1^2=R^2 at hc
    rw [HalfPlaneLine.extendedCircle,metricCircleAtI,complexCircle_realModel _ _ hR,
      complexCircle_realModel _ _ (Real.sinh_pos_iff.mpr hr),Inversive.inversiveProduct_sphere_sphere,
      ←map_sub,Mobius.complexPlaneCoordinates.norm_map]
    have hn : ‖(c : ℂ)-(Real.cosh r : ℂ)*Complex.I‖^2=c^2+Real.cosh r^2 := by
      rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
      simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero]
      ring
    rw [hn,show R^2+Real.sinh r^2-(c^2+Real.cosh r^2)=0 by nlinarith [Real.cosh_sq_sub_sinh_sq r],
      zero_div,abs_zero]

theorem hMetricCircle_realGL_image (p : ℍ) (r : ℝ) (g : GL (Fin 2) ℝ) :
    hMetricCircle (g • p) r=(g • · : ℍ → ℍ) '' hMetricCircle p r := by
  ext z
  constructor
  · intro hz
    refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
    change dist (g⁻¹ • z) p=r
    rw [←(realGL_isometry g).dist_eq (g⁻¹ • z) p,smul_inv_smul]
    exact hz
  · rintro ⟨w,hw,rfl⟩
    change dist (g • w) (g • p)=r
    rw [(realGL_isometry g).dist_eq]
    exact hw

/-- P3 for every actual H center and every genuine positive metric circle. -/
theorem hMetricCircle_orthogonal (p : ℍ) (r : ℝ) (hr : 0<r)
    (L : HalfPlaneLine) (hL : L∈hEllipticPencil p) :
    ∃C : Mobius.ComplexGeneralizedCircle,hMetricCircle p r=halfPlaneCircleCarrier C ∧
      Mobius.ComplexCirclesOrthogonal L.extendedCircle C := by
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ p.toSL2R
  have hg : 0<g.val.det:=by change 0<p.toSL2R.val.det; rw [p.toSL2R.property]; norm_num
  have hgp : g • UpperHalfPlane.I=p:=UpperHalfPlane.toSL2R_smul_I p
  let N:=L.realGLMap g⁻¹
  have hN : UpperHalfPlane.I∈N.carrier := by
    have he:=L.realGLMap_mem_carrier g⁻¹ p
    have hp' : g⁻¹ • p=UpperHalfPlane.I:=by rw [←hgp,inv_smul_smul]
    rw [hp'] at he
    exact he.mpr hL
  refine ⟨(metricCircleAtI r hr).image (geodesicRealGLMobius g),?_,?_⟩
  · rw [halfPlaneCircleCarrier_realGL_image _ g hg,←hMetricCircle_I_eq_circleCarrier,
      ←hMetricCircle_realGL_image,hgp]
  · have hNL : N.realGLMap g=L:=by simpa only [N,inv_inv] using L.realGLMap_inv g⁻¹
    rw [←hNL,←N.extendedCircle_image_realGL _ g hg (N.realGLMap_carrier g).symm]
    exact (metricCircleAtI_orthogonal r hr N hN).image _ _ _


theorem hMetricCircle_pair_dist_lower (p : ℍ) (r s : ℝ) {z w : ℍ}
    (hz : z∈hMetricCircle p r) (hw : w∈hMetricCircle p s) : |r-s|≤dist z w := by
  have h1:=dist_triangle z w p
  have h2:=dist_triangle w z p
  rw [dist_comm w z] at h2
  change dist z p=r at hz
  change dist w p=s at hw
  rw [hz,hw] at h1 h2
  apply abs_le.mpr
  constructor <;> linarith

/-- A genuine complete real-isometric geodesic provides the actual radial minimizing mate. -/
theorem isometry_real_exists_radial_mate (γ : ℝ → ℍ) (hγ : Isometry γ) (a b s : ℝ) (hs : 0≤s) :
    ∃t : ℝ,dist (γ t) (γ a)=s ∧ dist (γ b) (γ t)=|dist (γ b) (γ a)-s| := by
  by_cases hab : a≤b
  · refine ⟨a+s,?_,?_⟩
    · rw [hγ.dist_eq,Real.dist_eq,show a+s-a=s by ring,abs_of_nonneg hs]
    · rw [hγ.dist_eq,hγ.dist_eq,Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hab)]
      congr 1
      ring
  · refine ⟨a-s,?_,?_⟩
    · rw [hγ.dist_eq,Real.dist_eq,show a-s-a= -s by ring,abs_neg,abs_of_nonneg hs]
    · rw [hγ.dist_eq,hγ.dist_eq,Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr (not_le.mp hab).le)]
      rw [show b-(a-s)= -(-(b-a)-s) by ring,abs_neg]

/-- P5: each point has a closest point on the other genuine metric circle, on the same pencil line. -/
theorem hMetricCircle_equidistance (p : ℍ) (r s : ℝ) (hr : 0<r) (hs : 0≤s)
    (z : ℍ) (hz : z∈hMetricCircle p r) :
    ∃w : ℍ,w∈hMetricCircle p s ∧ dist z w=hCurveDistance (hMetricCircle p r) (hMetricCircle p s) ∧
      dist z w=|r-s| ∧ ∃L : HalfPlaneLine,L∈hEllipticPencil p ∧ z∈L.carrier ∧ w∈L.carrier := by
  have hzp : z≠p:=by intro he; subst z; change dist p p=r at hz; rw [dist_self] at hz; linarith
  obtain ⟨L,hp,hzL⟩:=exists_halfPlaneLine_through p z hzp.symm
  obtain ⟨γ,hγ,hrange⟩:=L.exists_isometric_param
  obtain ⟨a,ha⟩:=hrange ▸ hp
  obtain ⟨b,hb⟩:=hrange ▸ hzL
  obtain ⟨t,hts,hdt⟩:=isometry_real_exists_radial_mate γ hγ a b s hs
  have hw : γ t∈hMetricCircle p s := by change dist (γ t) p=s; rwa [ha] at hts
  have hd : dist z (γ t)=|r-s| := by
    rw [ha,hb] at hdt
    change dist z p=r at hz
    rwa [hz] at hdt
  refine ⟨γ t,hw,?_,hd,L,hp,hzL,hrange ▸ mem_range_self t⟩
  symm
  apply hCurveDistance_eq_of_min _ _ z (γ t) hz hw
  intro u hu v hv
  rw [hd]
  exact hMetricCircle_pair_dist_lower p r s hu hv

theorem hMetricCircle_curveDistance (p : ℍ) (r s : ℝ) (hr : 0<r) (hs : 0≤s) :
    hCurveDistance (hMetricCircle p r) (hMetricCircle p s)=|r-s| := by
  obtain ⟨z,hz⟩:=hMetricCircle_nonempty p r hr.le
  obtain ⟨w,hw,hd,hlen,_,_,_,_⟩:=hMetricCircle_equidistance p r s hr hs z hz
  exact hd.symm.trans hlen

end
end LowDimensionalTopology.Geometry.Hyperbolic
