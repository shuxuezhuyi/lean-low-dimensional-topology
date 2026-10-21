/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticMinimizers
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ParabolicReflectionPencils
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicProducts
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementDetermination
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual upper vertical ray contains a genuine point balancing elliptic and parabolic weights. -/
theorem exists_balanced_vertical_point (u : ℍ) (A C : ℝ) (hA : 0<A) (hC : 0<C) :
    ∃ z : ℍ,z.re=u.re ∧ u.im≤z.im ∧
      A*Real.sinh (dist u z)=C/(2*z.im) := by
  let y:=Real.sqrt (u.im^2+C*u.im/A)
  have hs : y^2=u.im^2+C*u.im/A := Real.sq_sqrt (by positivity)
  have hy0 : 0≤y := Real.sqrt_nonneg _
  have hy : u.im≤y := by nlinarith [div_pos (mul_pos hC u.im_pos) hA]
  have hyp : 0<y := u.im_pos.trans_le hy
  let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe u.re y hyp
  refine ⟨z,rfl,hy,?_⟩
  have hd : dist u z=Real.log (y/u.im) := by
    rw [dist_comm,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metric_vertical_distance (show z.re=u.re from rfl)]
    change |Real.log (y/u.im)|=Real.log (y/u.im)
    exact abs_of_nonneg (Real.log_nonneg ((one_le_div u.im_pos).mpr hy))
  rw [hd,Real.sinh_log (div_pos hyp u.im_pos)]
  change A*((y/u.im-(y/u.im)⁻¹)/2)=C/(2*y)
  rw [inv_div]
  have he : A*(y^2-u.im^2)=C*u.im := by
    rw [hs]
    field_simp
    ring
  field_simp
  nlinarith [he]

/-- Moving to the upper vertical ray gives the true global balanced minimum. -/
theorem balanced_vertical_point_minimizes (u z : ℍ) (hz : z.re=u.re)
    (hy : u.im≤z.im) (A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (hbal : A*Real.sinh (dist u z)=C/(2*z.im)) (w : ℍ) :
    max (A*Real.sinh (dist u z)) (C/(2*z.im))≤
      max (A*Real.sinh (dist u w)) (C/(2*w.im)) := by
  rw [hbal,max_self]
  by_cases hw : w.im≤z.im
  · exact (div_le_div_of_nonneg_left hC (by positivity : 0<2*w.im)
      (by linarith : 2*w.im≤2*z.im)).trans (le_max_right _ _)
  · have hloguz : Real.log u.im≤Real.log z.im := Real.log_le_log u.im_pos hy
    have hlogzw : Real.log z.im≤Real.log w.im := Real.log_le_log z.im_pos (le_of_not_ge hw)
    have hdz : dist u z=Real.log z.im-Real.log u.im := by
      rw [UpperHalfPlane.dist_of_re_eq hz.symm,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hloguz)]
      ring
    have hd : dist u z≤dist u w := by
      rw [hdz]
      have hb:=UpperHalfPlane.dist_log_im_le u w
      rw [Real.dist_eq,abs_sub_comm] at hb
      exact (by linarith : Real.log z.im-Real.log u.im≤Real.log w.im-Real.log u.im).trans
        ((le_abs_self _).trans hb)
    rw [←hbal]
    exact (mul_le_mul_of_nonneg_left (Real.sinh_le_sinh.mpr hd) hA).trans (le_max_left _ _)

/-- The radial/height formulas imply actual attainment of the plane-wide infimum. -/
theorem parabolic_radial_displacementM_attained (g h : ℍ ≃ᵢ ℍ) (u : ℍ) (A C : ℝ)
    (hA : 0<A) (hC : 0<C)
    (hg : ∀ z : ℍ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement g z=A*Real.sinh (dist u z))
    (hh : ∀ z : ℍ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement h z=C/(2*z.im)) :
    ∃ z : ℍ,z.re=u.re ∧ u.im≤z.im ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement g z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement h z ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM g h=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement g z := by
  obtain ⟨z,hz,hy,hbal⟩:=exists_balanced_vertical_point u A C hA hC
  refine ⟨z,hz,hy,?_,?_⟩
  · rw [hg,hh];exact hbal
  · apply le_antisymm
    · rw [hg]
      have he:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_le g h z
      rwa [hg,hh,←hbal,max_self] at he
    · apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_lower_bound _ _ _).mpr
      intro w
      rw [hg,hg,hh]
      have he:=balanced_vertical_point_minimizes u z hz hy A C hA.le hC.le hbal w
      rwa [←hbal,max_self] at he

/-- Every actual translation and actual elliptic map construct their true ray minimizer. -/
theorem translation_elliptic_displacementM_attained
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (t : ℝ) (ht : t≠0) :
    let u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
    ∃ z : ℍ,z.re=u.re ∧ u.im≤z.im ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) z := by
  obtain ⟨a,b,hu,hb,hdisp,_⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_half_displacement B hB
  have hg : ∀ z : ℍ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z=
      |b| *Real.sinh (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)) z) := by
    intro z
    change Real.sinh (dist z (B•z)/2)=_
    rw [hdisp,mul_comm,dist_comm]
  have hh : ∀ z : ℍ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) z=|t|/(2*z.im) := by
    intro z
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.translation_half_displacement t z
  obtain ⟨z,hz,hy,hbal,hM⟩:=parabolic_radial_displacementM_attained _ _ _ |b| |t|
    (abs_pos.mpr hb) (abs_pos.mpr ht) hg hh
  refine ⟨z,hz,hy,hbal.symm,?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_comm,hM,hbal]

/-- Arbitrary original parabolic/elliptic maps construct both a true joining-ray chart and
an actual equal-displacement minimizer; no conjugacy, center or normal form is assumed. -/
theorem parabolic_elliptic_displacementM_attained
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    ∃ (q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ)
      (hBQ : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹))),
      t≠0 ∧ (q*A*q⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t ∨ q*A*q⁻¹=
        -_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) ∧
      ∃ z : ℍ,
        let u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter (q*B*q⁻¹) ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ hBQ.1).mp hBQ)
        (q•z).re=u.re ∧ u.im≤(q•z).im ∧
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z ∧
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z := by
  obtain ⟨q,t,ht,hnorm⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  have hc : IsConj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)) := by
    apply isConj_iff.mpr
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q,?_⟩
    simp only [map_mul,map_inv]
  have hBQ:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_isConj hc).mp hB
  obtain ⟨w,hw,hy,hbal,hM⟩:=translation_elliptic_displacementM_attained _ hBQ t ht
  let z : ℍ:=q⁻¹•w
  have hqz : q•z=w := by simp only [z,smul_smul,mul_inv_cancel,one_smul]
  have hnormI : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) := by
    rcases hnorm with he | he
    · rw [he]
    · rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_neg]
  have hd (X : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*X*q⁻¹)) w=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X) z := by
    rw [hSLIsometry_conjugation,←hqz]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement_conjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry q) z
  have hdA:=hd A
  rw [hnormI] at hdA
  refine ⟨q,t,hBQ,ht,hnorm,z,?_,?_,?_,?_⟩
  · rwa [hqz]
  · rwa [hqz]
  · exact hdA.symm.trans (hbal.trans (hd B))
  · rw [←hnormI,hSLIsometry_conjugation A q,hSLIsometry_conjugation B q,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_conjugation] at hM
    exact hM.trans (by simpa only [hSLIsometry_conjugation] using hd A)

/-- The original geometric Mobius maps construct all their real lifts and their common minimizer. -/
theorem mobius_parabolic_elliptic_minimizer (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hg : g.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hpar : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) (hell :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    ∃ (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=f ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B=g ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z := by
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL f hf
  obtain ⟨B,hB⟩:=mobius_preserves_halfPlane_exists_SL g hg
  obtain ⟨q,t,hBQ,_ht,_hn,z,_hr,_hy,heq,hM⟩:=
    parabolic_elliptic_displacementM_attained A B (by rwa [hA]) (by rwa [hB])
  exact ⟨A,B,z,hA,hB,heq,hM⟩

end LowDimensionalTopology.Geometry.Fuchsian
