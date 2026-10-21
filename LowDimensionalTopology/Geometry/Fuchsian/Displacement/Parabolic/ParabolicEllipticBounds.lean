/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicEllipticMinimizers
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.EllipticProducts
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.QuarterSharpness
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicHalfTurns
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

/-- Exact actual maximum-displacement infimum for an elliptic radial map and parabolic height map. -/
theorem parabolic_radial_displacementM_square (g h : ℍ ≃ᵢ ℍ) (u : ℍ) (A C : ℝ)
    (hA : 0<A) (hC : 0<C)
    (hg : ∀ z : ℍ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement g z=A*Real.sinh (dist u z))
    (hh : ∀ z : ℍ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement h z=C/(2*z.im)) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM g h)^2=A*C^2/(4*u.im*(A*u.im+C)) := by
  obtain ⟨z,hz,hy,hbal,hM⟩:=parabolic_radial_displacementM_attained g h u A C hA hC hg hh
  rw [hg,hh] at hbal
  rw [hg,hbal] at hM
  have hd : dist u z=Real.log (z.im/u.im) := by
    rw [dist_comm,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metric_vertical_distance hz]
    exact abs_of_nonneg (Real.log_nonneg ((one_le_div u.im_pos).mpr hy))
  rw [hd,Real.sinh_log (div_pos z.im_pos u.im_pos),inv_div] at hbal
  have he : A*(z.im^2-u.im^2)=C*u.im := by
    field_simp at hbal
    nlinarith [hbal]
  have hden : 4*u.im*(A*u.im+C)=4*A*z.im^2 := by nlinarith [he]
  rw [hM,hden]
  field_simp
  ring

/-- The actual elliptic half-sine weight equals the absolute lower-left coefficient times height. -/
theorem elliptic_actual_angle_height (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2)=
      |B 1 0| *(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)).im := by
  have hs : 0<Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_pos B hB])
      (by linarith [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec B hB).1.2])
  have he:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_half_angle_coefficients B hB
  rcases he with ⟨_,he⟩|⟨_,he⟩
  all_goals
    have hx:=congrArg abs he
    simpa only [abs_mul,abs_neg,abs_of_pos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B
      _).im_pos,abs_of_pos hs] using hx.symm

/-- An actual translation/elliptic pair satisfies the exact formula derived. -/
theorem translation_elliptic_displacementM_square
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (t : ℝ) (ht : t≠0) :
    let u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
    let s:=Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2=
      s*t^2/(4*u.im*(s*u.im+|t|)) := by
  have hs : 0<Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_pos B hB])
      (by linarith [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec B hB).1.2])
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_comm]
  have he:=parabolic_radial_displacementM_square (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))
    (Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2)) |t| hs (abs_pos.mpr ht)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_actual_angle_radial B hB) (by intro z;exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.translation_half_displacement t z)
  simpa only [sq_abs] using he

/-- The numerical estimate uses the actual coefficient constraint and the genuine sine range. -/
theorem parabolic_radial_quotient_eighth (A C v : ℝ) (hA : 0<A) (hA1 : A≤1)
    (hC : 0<C) (hv : 0<v) (hbound : v≤C*A) :
    1/8≤A*C^2/(4*v*(A*v+C)) := by
  have hA2 : A^2≤1 := by nlinarith
  have hAv : A*v≤C := by
    have hm:=mul_le_mul_of_nonneg_left hbound hA.le
    have hm2:=mul_le_mul_of_nonneg_left hA2 hC.le
    nlinarith [hm,hm2]
  have hm:=mul_le_mul hbound (by linarith : A*v+C≤2*C)
    (by positivity : 0≤A*v+C) (by positivity : 0≤C*A)
  apply (le_div_iff₀ (by positivity : 0<4*v*(A*v+C))).mpr
  nlinarith [hm]

/-- The genuine discrete non-elementary translation/elliptic pair satisfies a uniform bound. -/
theorem translation_elliptic_displacementM_eighth
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (t : ℝ) (ht : t≠0)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/8≤(_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2 := by
  let u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
  let s:=Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2)
  have hs : 0<s :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_pos B hB])
      (by linarith [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec B hB).1.2])
  have hj:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.one_le_jorgensenDefect_of_discrete_nonElementary _ _ hd hne
  rw [translation_jorgensen_defect,abs_mul] at hj
  have hj1 : 1≤|t| *|B 1 0| := by nlinarith [mul_nonneg (abs_nonneg t) (abs_nonneg (B 1 0))]
  have he : s=|B 1 0| *u.im := elliptic_actual_angle_height B hB
  have hv : u.im≤|t| *s := by
    have hm:=mul_le_mul_of_nonneg_right hj1 u.im_pos.le
    rw [he]
    nlinarith [hm]
  rw [translation_elliptic_displacementM_square B hB t ht]
  change 1/8≤s*t^2/(4*u.im*(s*u.im+|t|))
  rw [←sq_abs t]
  exact parabolic_radial_quotient_eighth s |t| u.im hs (Real.sin_le_one _)
    (abs_pos.mpr ht) u.im_pos hv

/-- The eighth bound transports to any actual parabolic/elliptic pair. -/
theorem parabolic_elliptic_displacementM_eighth (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/8≤(_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2 := by
  obtain ⟨q,t,_ht,hnorm⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  have hprojA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) := by
    rw [←map_inv,←map_mul,←map_mul]
    rcases hnorm with he | he
    · rw [he]
    · rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg]
  have hprojB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹) := by
    simp only [map_mul,map_inv]
  let H := Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hD' : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    let : DiscreteTopology H := hd
    have he := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H
    change DiscreteTopology (H.map (MulAut.conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      q)).toMonoidHom) at he
    dsimp only [H] at he
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation, hprojA,hprojB] at he
    exact he
  have hN' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    have he := hne.conjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,hprojA,hprojB] at he
    exact he
  have hnormI : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) := by
    rcases hnorm with he | he
    · rw [he]
    · rw [he]
      apply IsometryEquiv.ext
      intro z
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_neg_smul _ z
  have hBq : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)) := by
    apply (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_isConj (isConj_iff.mpr
      ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q,rfl⟩)).mp at hB
    simpa only [map_mul,map_inv] using hB
  have hb:=translation_elliptic_displacementM_eighth (q*B*q⁻¹) hBq t _ht hD' hN'
  rw [←hnormI,hSLIsometry_conjugation A q,hSLIsometry_conjugation B q,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_conjugation] at hb
  exact hb

/-- In the original arbitrary geometric pair, the displacement maximum is at least 1/√8. -/
theorem parabolic_elliptic_displacementM_sqrt_eighth (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/Real.sqrt 8≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  have he:=parabolic_elliptic_displacementM_eighth A B hA hB hd hne
  have hs : Real.sqrt (1/8)≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) :=
    Real.sqrt_le_iff.mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _,he⟩
  rw [Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one] at hs
  exact hs

/-- The actual unit-height half-turn is the modular negative reciprocal generator. -/
theorem unitHalfTurn_projection :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 (by norm_num))=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion := by
  change _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection
    (Matrix.SpecialLinearGroup.map Complex.ofRealHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 (by norm_num)))=
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversionLift
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversionLift]

/-- The literal parabolic/half-turn pair generates the already verified actual modular group. -/
theorem unitHalfTurn_translation_group :
    Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 (by norm_num))} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup := by
  rw [quarterTranslation_projection,unitHalfTurn_projection]
  rfl

/-- This actual group attains the lower bound, as a true infimum over the whole plane. -/
theorem unitHalfTurn_translation_displacementM_square :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 (by norm_num))))^2=1/8 := by
  have hhalf:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at 1 (by norm_num)
  have hcenter : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 (by norm_num))
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ hhalf.elliptic.1).mp
        hhalf.elliptic)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 1 (by norm_num) :=
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff _ _ _).mp hhalf.2).symm
  have he:=translation_elliptic_displacementM_square _ hhalf.elliptic 1 (by norm_num)
  dsimp only at he
  rw [hhalf.rotation_angle,hcenter] at he
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] at he
  exact he

/-- The half-turn lower bound is attained by a genuinely discrete non-elementary pair. -/
theorem unitHalfTurn_translation_sharp :
    _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 (by norm_num))} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 (by norm_num))} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 (by norm_num)))=1/Real.sqrt 8 := by
  refine ⟨?_,?_,?_⟩
  · rw [unitHalfTurn_translation_group]
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup_discrete
  · rw [unitHalfTurn_translation_group]
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup_nonElementary
  · have he:=unitHalfTurn_translation_displacementM_square
    have hs : ((1:ℝ)/Real.sqrt 8)^2=1/8 := by norm_num [div_pow,Real.sq_sqrt]
    have hn:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 (by norm_num)))
    nlinarith [show (0:ℝ)≤1/Real.sqrt 8 by positivity]

end LowDimensionalTopology.Geometry.Fuchsian
