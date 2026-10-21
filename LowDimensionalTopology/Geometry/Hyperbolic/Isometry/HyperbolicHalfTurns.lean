/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HyperbolicReflectionPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalRegions
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticRotationAngles
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine half-turn is an actual order-two conformal isometry with its actual center. -/
def IsHalfTurnAt (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (v : ℍ) : Prop :=
  orderOf (realSLMobius A)=2 ∧ A•v=v

theorem IsHalfTurnAt.ne_one {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {v : ℍ}
    (h : IsHalfTurnAt A v) : realSLMobius A≠1 := by
  intro he
  have hh := h.1
  rw [he,orderOf_one] at hh
  norm_num at hh

theorem IsHalfTurnAt.elliptic {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {v : ℍ}
    (h : IsHalfTurnAt A v) : Mobius.MobiusElliptic (realSLMobius A) :=
  realSLMobius_elliptic_of_fixed A h.ne_one v h.2

/-- Its true source rotation angle is pi. -/
theorem IsHalfTurnAt.rotation_angle {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {v : ℍ}
    (h : IsHalfTurnAt A v) : hEllipticRotationAngle A h.elliptic=Real.pi := by
  have ht := (realSLMobius_order_two_iff_trace_zero A h.ne_one).mp h.1
  have hp := hEllipticRotationAngle_spec A h.elliptic
  have hcos : Real.cos (hEllipticRotationAngle A h.elliptic/2)=0 := by
    have hh := hp.2.2.2
    rw [ht] at hh
    nlinarith [sq_nonneg (Real.cos (hEllipticRotationAngle A h.elliptic/2))]
  have he := Real.strictAntiOn_cos.injOn
    (show hEllipticRotationAngle A h.elliptic/2 ∈ Icc 0 Real.pi from ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩)
    (show Real.pi/2 ∈ Icc 0 Real.pi from ⟨by positivity,by linarith [Real.pi_pos]⟩)
    (show Real.cos (hEllipticRotationAngle A h.elliptic/2)=Real.cos (Real.pi/2) by rw [hcos,Real.cos_pi_div_two])
  linarith

/-- A genuine center determines the entire actual half-turn map. -/
theorem IsHalfTurnAt.unique {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ} {v : ℍ}
    (hA : IsHalfTurnAt A v) (hB : IsHalfTurnAt B v) : realSLMobius A=realSLMobius B := by
  apply realSLMobius_elliptic_eq_of_center_angle A B hA.elliptic hB.elliptic
  · have hcA := (hSL_elliptic_fixed_iff A ((realSLMobius_elliptic_iff A hA.ne_one).mp hA.elliptic) v).mp hA.2
    have hcB := (hSL_elliptic_fixed_iff B ((realSLMobius_elliptic_iff B hB.ne_one).mp hB.elliptic) v).mp hB.2
    exact hcA.symm.trans hcB
  · exact hA.rotation_angle.trans hB.rotation_angle.symm

/-- The literal imaginary-axis half-turn has exact real determinant one. -/
def axisHalfTurnSL (a : ℝ) (ha : 0<a) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![0,-a;1/a,0],by simp [Matrix.det_fin_two,ha.ne']⟩

theorem axisHalfTurnSL_coe (a : ℝ) (ha : 0<a) (z : ℍ) :
    ((axisHalfTurnSL a ha•z : ℍ):ℂ)=-(a:ℂ)^2/(z:ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self_apply]
  change ((0:ℂ)*z+((-a:ℝ):ℂ)) / (((1/a:ℝ):ℂ)*z+(0:ℂ))= _
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ha.ne',z.ne_zero]
  ring

theorem axisHalfTurnSL_trace (a : ℝ) (ha : 0<a) : Matrix.trace (axisHalfTurnSL a ha).val=0 := by
  simp [axisHalfTurnSL,Matrix.trace_fin_two]

theorem realSL_trace_zero_ne_one (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace A.val=0) : realSLMobius A≠1 := by
  intro he
  have h1 : Mobius.mobiusSquaredTrace (1:Mobius.complexMobiusGroup)=(4:ℂ) := by
    have hh := realSLMobius_squaredTrace (1:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    norm_num [Matrix.trace_fin_two] at hh
    exact hh
  have hh := congrArg Mobius.mobiusSquaredTrace he
  rw [realSLMobius_squaredTrace,ht,h1] at hh
  norm_num at hh

/-- The literal matrix is a genuine rotation of order two about its literal metric center. -/
theorem axisHalfTurnSL_at (a : ℝ) (ha : 0<a) :
    IsHalfTurnAt (axisHalfTurnSL a ha) (metricProbe 0 a ha) := by
  refine ⟨(realSLMobius_order_two_iff_trace_zero _
    (realSL_trace_zero_ne_one _ (axisHalfTurnSL_trace a ha))).mpr (axisHalfTurnSL_trace a ha),?_⟩
  apply UpperHalfPlane.ext
  rw [axisHalfTurnSL_coe]
  have hp : ((metricProbe 0 a ha:ℍ):ℂ)=(a:ℂ)*Complex.I := by
    apply Complex.ext <;> simp [metricProbe]
  rw [hp]
  field_simp [Complex.ofReal_ne_zero.mpr ha.ne',Complex.I_ne_zero]
  simp [Complex.I_sq]

/-- Two literal imaginary-axis half-turns compose to the genuine positive dilation. -/
theorem axisHalfTurns_product_coe (a b : ℝ) (ha : 0<a) (hb : 0<b) (z : ℍ) :
    (((axisHalfTurnSL b hb*axisHalfTurnSL a ha)•z : ℍ):ℂ)=((b/a:ℝ):ℂ)^2*z := by
  rw [mul_smul,axisHalfTurnSL_coe,axisHalfTurnSL_coe]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ha.ne',z.ne_zero]

/-- Half-turns and their actual centers transport under genuine real SL conjugacy. -/
theorem IsHalfTurnAt.conjugate {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {v : ℍ}
    (h : IsHalfTurnAt A v) (q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    IsHalfTurnAt (q*A*q⁻¹) (q•v) := by
  constructor
  · rw [map_mul,map_mul,map_inv]
    have hc : SemiconjBy (realSLMobius q) (realSLMobius A)
        (realSLMobius q*realSLMobius A*(realSLMobius q)⁻¹) := by
      change realSLMobius q*realSLMobius A=
        (realSLMobius q*realSLMobius A*(realSLMobius q)⁻¹)*realSLMobius q
      group
    exact (SemiconjBy.orderOf_eq (realSLMobius q) hc).symm.trans h.1
  · simp only [mul_smul,inv_smul_smul,h.2]

theorem IsHalfTurnAt.fixed_iff {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {v : ℍ}
    (h : IsHalfTurnAt A v) (z : ℍ) : A•z=z ↔ z=v := by
  have hc := (hSL_elliptic_fixed_iff A ((realSLMobius_elliptic_iff A h.ne_one).mp h.elliptic) v).mp h.2
  rw [hSL_elliptic_fixed_iff A ((realSLMobius_elliptic_iff A h.ne_one).mp h.elliptic),←hc]

/-- A factorization uses the actual full Mobius map and actual native centers. -/
def HasHalfTurnFactorization (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) (v w : ℍ) : Prop :=
  ∃ A B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
    IsHalfTurnAt A v ∧ IsHalfTurnAt B w ∧ realSLMobius f=realSLMobius B*realSLMobius A

/-- Prescribing either the action and the first center determines the other actual center. -/
theorem halfTurnFactorization_partner_unique (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) (v w w' : ℍ)
    (h : HasHalfTurnFactorization f v w) (h' : HasHalfTurnFactorization f v w') : w=w' := by
  obtain ⟨A,B,hA,hB,he⟩ := h
  obtain ⟨A',B',hA',hB',he'⟩ := h'
  have hAe := hA.unique hA'
  rw [←hAe] at he'
  have hBe : realSLMobius B=realSLMobius B' := mul_right_cancel (he.symm.trans he')
  have hfix : B•w'=w' := by
    apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    rw [←realSLMobius_action,hBe,realSLMobius_action,hB'.2]
  exact ((hB.fixed_iff w').mp hfix).symm

/-- Every positive dilation is the actual product of the two indicated literal half-turns. -/
theorem axisHalfTurns_dilation_action (k a : ℝ) (hk : 0<k) (ha : 0<a) (z : ℍ) :
    (axisHalfTurnSL (Real.sqrt k*a) (mul_pos (Real.sqrt_pos.mpr hk) ha)*axisHalfTurnSL a ha)•z=
      verticalDilationSL k hk•z := by
  apply UpperHalfPlane.ext
  rw [axisHalfTurns_product_coe,verticalDilationSL_coe]
  have hr : (Real.sqrt k*a)/a=Real.sqrt k := by field_simp [ha.ne']
  rw [hr]
  have hs : (Real.sqrt k:ℂ)^2=(k:ℂ) := by exact_mod_cast Real.sq_sqrt hk.le
  rw [hs]

/-- A genuine translation normal form transports a complete half-turn family to the original action. -/
theorem realSL_halfturn_family_of_normalizer (f q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (k : ℝ) (hk : 0<k)
    (hact : ∀ z : ℍ, (q*f*q⁻¹)•z=verticalDilationSL k hk•z)
    (a : ℝ) (ha : 0<a) :
    HasHalfTurnFactorization f (q⁻¹•metricProbe 0 a ha)
      (q⁻¹•metricProbe 0 (Real.sqrt k*a) (mul_pos (Real.sqrt_pos.mpr hk) ha)) := by
  let b := Real.sqrt k*a
  have hb : 0<b := mul_pos (Real.sqrt_pos.mpr hk) ha
  let A := q⁻¹*axisHalfTurnSL a ha*q
  let B := q⁻¹*axisHalfTurnSL b hb*q
  refine ⟨A,B,?_,?_,?_⟩
  · simpa only [inv_inv] using (axisHalfTurnSL_at a ha).conjugate q⁻¹
  · simpa only [inv_inv] using (axisHalfTurnSL_at b hb).conjugate q⁻¹
  · rw [←map_mul]
    apply realSLMobius_ext_action
    intro z
    have h := congrArg (fun w : ℍ => q⁻¹•w) (hact (q•z))
    simp only [mul_smul,inv_smul_smul] at h
    calc
      f•z=q⁻¹•(verticalDilationSL k hk•(q•z)) := h
      _=(B*A)•z := by
        dsimp only [A,B,b]
        simp only [mul_smul,smul_inv_smul]
        have hh := axisHalfTurns_dilation_action k a hk ha (q•z)
        rw [mul_smul] at hh
        exact congrArg (fun w : ℍ => q⁻¹•w) hh.symm


theorem imaginaryAxisParam_log_metricProbe (a : ℝ) (ha : 0<a) :
    imaginaryAxisParam (Real.log a)=metricProbe 0 a ha := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · rfl
  · change Real.exp (Real.log a)=a
    exact Real.exp_log ha

theorem imaginaryAxisParam_isHGeodesicParam : IsHGeodesicParam imaginaryAxisParam := by
  refine ⟨imaginaryAxisParam_isometry,?_⟩
  have hr : range imaginaryAxisParam=(HalfPlaneLine.vertical 0).carrier := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      rfl
    · intro hz
      refine ⟨Real.log z.im,?_⟩
      apply UpperHalfPlane.ext
      apply Complex.ext
      · exact hz.symm
      · exact Real.exp_log z.im_pos
  rw [hr]
  exact (HalfPlaneLine.vertical 0).isHLine

theorem hRayThrough_axis_idealEndpoint (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (hne : metricProbe 0 a ha≠metricProbe 0 b hb) :
    (hRayThrough (metricProbe 0 a ha) (metricProbe 0 b hb) hne).idealEndpoint=
      if a<b then (∞ : OnePoint ℂ) else ((0 : ℂ) : OnePoint ℂ) := by
  split_ifs with hab
  · let R : HRayAt (metricProbe 0 a ha):=
      ⟨forwardHLineRay imaginaryAxisParam (Real.log a),∞,by simp [halfPlaneIdealBoundary],
        imaginaryAxisParam,imaginaryAxisParam_isHGeodesicParam,Real.log a,
        imaginaryAxisParam_log_metricProbe a ha,Or.inl rfl,imaginaryAxis_forwardRay_idealEndpoints _⟩
    have hw : metricProbe 0 b hb∈R.val := by
      exact ⟨Real.log b,(Real.strictMonoOn_log ha hb hab).le,imaginaryAxisParam_log_metricProbe b hb⟩
    rw [hRayThrough_eq hne R hw]
    exact R.idealEndpoint_unique ⟨imaginaryAxisParam,imaginaryAxisParam_isHGeodesicParam,Real.log a,
      imaginaryAxisParam_log_metricProbe a ha,Or.inl rfl,imaginaryAxis_forwardRay_idealEndpoints _⟩
  · let R : HRayAt (metricProbe 0 a ha):=
      ⟨backwardHLineRay imaginaryAxisParam (Real.log a),(0 : ℂ),by simp [coe_mem_halfPlaneIdealBoundary],
        imaginaryAxisParam,imaginaryAxisParam_isHGeodesicParam,Real.log a,
        imaginaryAxisParam_log_metricProbe a ha,Or.inr rfl,imaginaryAxis_backwardRay_idealEndpoints _⟩
    have hw : metricProbe 0 b hb∈R.val := by
      exact ⟨Real.log b,Real.strictMonoOn_log.monotoneOn hb ha (not_lt.mp hab),
        imaginaryAxisParam_log_metricProbe b hb⟩
    rw [hRayThrough_eq hne R hw]
    exact R.idealEndpoint_unique ⟨imaginaryAxisParam,imaginaryAxisParam_isHGeodesicParam,Real.log a,
      imaginaryAxisParam_log_metricProbe a ha,Or.inr rfl,imaginaryAxis_backwardRay_idealEndpoints _⟩

theorem halfTurn_axis_height_ne (a k : ℝ) (ha : 0<a) (hk : 0<k) (hk1 : k≠1) :
    metricProbe 0 a ha≠metricProbe 0 (Real.sqrt k*a) (mul_pos (Real.sqrt_pos.mpr hk) ha) := by
  intro he
  have hi:=congrArg UpperHalfPlane.im he
  change a=Real.sqrt k*a at hi
  have hs : Real.sqrt k=1:=by nlinarith
  exact hk1 (Real.sqrt_eq_one.mp hs)

theorem halfTurn_axis_ray_idealEndpoint (a k : ℝ) (ha : 0<a) (hk : 0<k) (hk1 : k≠1) :
    (hRayThrough (metricProbe 0 a ha)
      (metricProbe 0 (Real.sqrt k*a) (mul_pos (Real.sqrt_pos.mpr hk) ha))
      (halfTurn_axis_height_ne a k ha hk hk1)).idealEndpoint=
        if 1<k then (∞ : OnePoint ℂ) else ((0 : ℂ) : OnePoint ℂ) := by
  rw [hRayThrough_axis_idealEndpoint]
  have he : a<Real.sqrt k*a ↔ 1<k := by
    calc
      a<Real.sqrt k*a ↔ (1 : ℝ)<Real.sqrt k := by
        simpa only [one_mul] using (mul_lt_mul_iff_left₀ ha : (1 : ℝ)*a<Real.sqrt k*a ↔ 1<Real.sqrt k)
      _ ↔ 1<k := by
        simpa only [Real.sqrt_one] using (Real.sqrt_lt_sqrt_iff (x:=1) (y:=k) (by norm_num : 0≤(1 : ℝ)))
  simp only [he]


def positiveScalingUnit (k : ℝ) (hk : 0<k) : ℂˣ :=
  Units.mk0 (k : ℂ) (Complex.ofReal_ne_zero.mpr hk.ne')

theorem positiveScaling_attracting_repelling (k : ℝ) (hk : 0<k) (hk1 : k≠1) :
    Mobius.IsMobiusAttractingRepellingPair (Mobius.mobiusStandardElement (positiveScalingUnit k hk))
      (if 1<k then (∞ : OnePoint ℂ) else ((0 : ℂ) : OnePoint ℂ))
      (if 1<k then ((0 : ℂ) : OnePoint ℂ) else (∞ : OnePoint ℂ)) := by
  by_cases h1 : 1<k
  · simp only [ite_eq_left h1]
    apply Mobius.mobius_standard_expansion_attracting_repelling
    change 1<‖(k : ℂ)‖
    rwa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk]
  · simp only [ite_eq_right h1]
    apply Mobius.mobius_standard_contraction_attracting_repelling
    change ‖(k : ℂ)‖<1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk]
    exact lt_of_le_of_ne (not_lt.mp h1) hk1

theorem halfTurn_axis_ray_endpoint_is_attractive (a k : ℝ) (ha : 0<a) (hk : 0<k) (hk1 : k≠1) :
    Mobius.MobiusAttractiveFixedPoint (Mobius.mobiusStandardElement (positiveScalingUnit k hk))
      (hRayThrough (metricProbe 0 a ha)
        (metricProbe 0 (Real.sqrt k*a) (mul_pos (Real.sqrt_pos.mpr hk) ha))
        (halfTurn_axis_height_ne a k ha hk hk1)).idealEndpoint := by
  rw [halfTurn_axis_ray_idealEndpoint a k ha hk hk1]
  exact ⟨_,positiveScaling_attracting_repelling k hk hk1⟩

/-- The literal two half-turn centers have their actual native distance. -/
theorem axis_halfturn_centers_dist (k a : ℝ) (hk : 0<k) (ha : 0<a) :
    dist (metricProbe 0 a ha) (metricProbe 0 (Real.sqrt k*a) (mul_pos (Real.sqrt_pos.mpr hk) ha))=
      |Real.log (Real.sqrt k)| := by
  rw [←imaginaryAxisParam_log_metricProbe a ha,
    ←imaginaryAxisParam_log_metricProbe (Real.sqrt k*a) (mul_pos (Real.sqrt_pos.mpr hk) ha),
    imaginaryAxisParam_isometry.dist_eq,Real.dist_eq,
    Real.log_mul (Real.sqrt_pos.mpr hk).ne' ha.ne']
  have he : Real.log a-(Real.log (Real.sqrt k)+Real.log a)= -Real.log (Real.sqrt k) := by ring
  rw [he,abs_neg]

/-- The positive translation length is twice the distance of those literal centers. -/
theorem axis_halfturn_twice_centers_dist (k a : ℝ) (hk : 0<k) (ha : 0<a) :
    2*dist (metricProbe 0 a ha) (metricProbe 0 (Real.sqrt k*a) (mul_pos (Real.sqrt_pos.mpr hk) ha))=
      |Real.log k| := by
  rw [axis_halfturn_centers_dist k a hk ha]
  have hl : Real.log k=2*Real.log (Real.sqrt k) := by
    calc
      Real.log k=Real.log ((Real.sqrt k)^2) := congrArg Real.log (Real.sq_sqrt hk.le).symm
      _=2*Real.log (Real.sqrt k) := by rw [Real.log_pow];norm_num
  rw [hl,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]

/-- Every actual point of the hyperbolic axis can be the first half-turn center;
the partner is unique, lies on that axis and has exactly half the translation distance. -/
theorem realSL_hyperbolic_halfturn_factor (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) (ht : 4<(Matrix.trace f.val)^2) (v : ℍ)
    (hv : v∈(hHyperbolicAxis f hf ht).carrier) :
    ∃! w : ℍ, w∈(hHyperbolicAxis f hf ht).carrier ∧ HasHalfTurnFactorization f v w ∧
      hTranslationLength (hSLIsometry f)=2*dist v w := by
  obtain ⟨q,k,hk,hk1,haxis,hT,hact⟩ := hHyperbolicAxis_normalizer f hf ht
  let a := (q•v).im
  have ha : 0<a := (q•v).im_pos
  have hv0 : (q•v).re=0 := by rw [haxis] at hv;exact hv
  have hpa : metricProbe 0 a ha=q•v := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hv0.symm
    · rfl
  have hvp : q⁻¹•metricProbe 0 a ha=v := by rw [hpa,inv_smul_smul]
  let p := metricProbe 0 (Real.sqrt k*a) (mul_pos (Real.sqrt_pos.mpr hk) ha)
  let w := q⁻¹•p
  have hw : w∈(hHyperbolicAxis f hf ht).carrier := by
    rw [haxis]
    change (q•(q⁻¹•p)).re=0
    rw [smul_inv_smul]
    rfl
  have hfact := realSL_halfturn_family_of_normalizer f q k hk hact a ha
  rw [hvp] at hfact
  have hd : dist v w=dist (metricProbe 0 a ha) p := by
    have hh := (realGL_isometry (Matrix.SpecialLinearGroup.mapGL ℝ q)).dist_eq v w
    change dist (q•v) (q•w)=dist v w at hh
    dsimp only [w] at hh
    rw [smul_inv_smul,←hpa] at hh
    exact hh.symm
  have hlength : hTranslationLength (hSLIsometry f)=2*dist v w := by
    rw [hT,hd,axis_halfturn_twice_centers_dist k a hk ha]
  exact ⟨w,⟨hw,hfact,hlength⟩,fun u hu =>halfTurnFactorization_partner_unique f v u w hu.2.1 hfact⟩

/-- The second half-turn sends the first center to its actual hyperbolic image. -/
theorem halfturn_second_maps_first (f A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (v w : ℍ)
    (hA : IsHalfTurnAt A v) (_hB : IsHalfTurnAt B w)
    (he : realSLMobius f=realSLMobius B*realSLMobius A) : B•v=f•v := by
  apply UpperHalfPlane.ext
  apply OnePoint.coe_injective
  rw [←realSLMobius_action,←realSLMobius_action,he]
  change (realSLMobius B).val ((v:ℂ):Mobius.ExtendedComplex)=
    (realSLMobius B).val ((realSLMobius A).val ((v:ℂ):Mobius.ExtendedComplex))
  rw [realSLMobius_action A v,hA.2,realSLMobius_action B v]

/-- Two genuine half-turns with distinct centers have a hyperbolic product. -/
theorem halfturn_factorization_hyperbolic (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) (v w : ℍ) (hvw : v≠w) (h : HasHalfTurnFactorization f v w) :
    Mobius.MobiusHyperbolic (realSLMobius f) := by
  obtain ⟨A,B,hA,hB,he⟩ := h
  obtain ⟨q,hv0,hw0,hab⟩ := exists_sl2_ordered_imaginary v w hvw
  let a := (q•v).im
  let b := (q•w).im
  have ha : 0<a := (q•v).im_pos
  have hb : 0<b := (q•w).im_pos
  have hpa : metricProbe 0 a ha=q•v := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hv0.symm
    · rfl
  have hpb : metricProbe 0 b hb=q•w := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hw0.symm
    · rfl
  have hAa : IsHalfTurnAt (axisHalfTurnSL a ha) (q•v) := by rw [←hpa];exact axisHalfTurnSL_at a ha
  have hBb : IsHalfTurnAt (axisHalfTurnSL b hb) (q•w) := by rw [←hpb];exact axisHalfTurnSL_at b hb
  have hAe := (hA.conjugate q).unique hAa
  have hBe := (hB.conjugate q).unique hBb
  let C := q*f*q⁻¹
  let k := (b/a)^2
  have hr : 1<b/a := (lt_div_iff₀ ha).mpr (by change a<b at hab;linarith)
  have hk : 0<k := sq_pos_of_pos (div_pos hb ha)
  have hk1 : k≠1 := by intro h;dsimp only [k] at h;nlinarith [hr]
  have hnorm : realSLMobius C=realSLMobius (axisHalfTurnSL b hb*axisHalfTurnSL a ha) := by
    simp only [C,map_mul,map_inv]
    rw [he]
    simp only [map_mul,map_inv] at hAe hBe
    calc
      realSLMobius q*(realSLMobius B*realSLMobius A)*(realSLMobius q)⁻¹=
        (realSLMobius q*realSLMobius B*(realSLMobius q)⁻¹)*
          (realSLMobius q*realSLMobius A*(realSLMobius q)⁻¹) := by group
      _=realSLMobius (axisHalfTurnSL b hb)*realSLMobius (axisHalfTurnSL a ha) := by rw [hAe,hBe]
  have hD : realSLMobius (axisHalfTurnSL b hb*axisHalfTurnSL a ha)=realSLMobius (verticalDilationSL k hk) := by
    apply realSLMobius_ext_action
    intro z
    apply UpperHalfPlane.ext
    rw [axisHalfTurns_product_coe,verticalDilationSL_coe]
    change (((b/a:ℝ):ℂ)^2)*(z:ℂ)=(((b/a)^2:ℝ):ℂ)*(z:ℂ)
    rw [Complex.ofReal_pow]
  have hproj : realSLMobius C=realSLMobius q*realSLMobius f*(realSLMobius q)⁻¹ := by
    simp only [C,map_mul,map_inv]
  have hn : realSLMobius C≠1 := by
    intro hh
    apply hf
    calc
      realSLMobius f=(realSLMobius q)⁻¹*(realSLMobius q*realSLMobius f*(realSLMobius q)⁻¹)*realSLMobius q := by group
      _=1 := by rw [←hproj,hh];simp
  have htr := congrArg Mobius.mobiusSquaredTrace (hnorm.trans hD)
  rw [realSLMobius_squaredTrace,realSLMobius_squaredTrace] at htr
  have htrR := Complex.ofReal_injective htr
  have hC : Mobius.MobiusHyperbolic (realSLMobius C) := by
    apply (realSLMobius_hyperbolic_iff C hn).mpr
    rw [htrR]
    exact verticalDilationSL_trace_gt_four k hk hk1
  exact (Mobius.mobiusHyperbolic_isConj (isConj_iff.mpr ⟨realSLMobius q,hproj.symm⟩)).mpr hC

/-- The genuine hyperbolic class is precisely the product of two actual half-turns at distinct centers. -/
theorem realSL_hyperbolic_iff_halfturn_factorization (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) :
    Mobius.MobiusHyperbolic (realSLMobius f) ↔ ∃ v w : ℍ, v≠w ∧ HasHalfTurnFactorization f v w := by
  constructor
  · intro hH
    have ht := (realSLMobius_hyperbolic_iff f hf).mp hH
    obtain ⟨q,k,hk,hk1,haxis,hT,hact⟩ := hHyperbolicAxis_normalizer f hf ht
    let v := q⁻¹•UpperHalfPlane.I
    have hv : v∈(hHyperbolicAxis f hf ht).carrier := by
      rw [haxis]
      change (q•(q⁻¹•UpperHalfPlane.I)).re=0
      rw [smul_inv_smul]
      rfl
    obtain ⟨w,hw,_⟩ := realSL_hyperbolic_halfturn_factor f hf ht v hv
    have hne : v≠w := by
      intro he
      have hl := hw.2.2
      rw [←he,dist_self,mul_zero] at hl
      have hp := hHyperbolic_translationLength_pos f hf ht
      linarith
    exact ⟨v,w,hne,hw.2.1⟩
  · rintro ⟨v,w,hne,h⟩
    exact halfturn_factorization_hyperbolic f hf v w hne h

/-- The action and second center uniquely determine the first actual half-turn center. -/
theorem halfTurnFactorization_first_unique (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) (v v' w : ℍ)
    (h : HasHalfTurnFactorization f v w) (h' : HasHalfTurnFactorization f v' w) : v=v' := by
  obtain ⟨A,B,hA,hB,he⟩ := h
  obtain ⟨A',B',hA',hB',he'⟩ := h'
  have hBe := hB.unique hB'
  rw [←hBe] at he'
  have hAe : realSLMobius A=realSLMobius A' := mul_left_cancel (he.symm.trans he')
  have hfix : A•v'=v' := by
    apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    rw [←realSLMobius_action,hAe,realSLMobius_action,hA'.2]
  exact ((hA.fixed_iff v').mp hfix).symm

/-- The second center can also be any prescribed actual point of the hyperbolic axis. -/
theorem realSL_hyperbolic_halfturn_factor_right (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) (ht : 4<(Matrix.trace f.val)^2) (v : ℍ)
    (hv : v∈(hHyperbolicAxis f hf ht).carrier) :
    ∃! u : ℍ, u∈(hHyperbolicAxis f hf ht).carrier ∧ HasHalfTurnFactorization f u v ∧
      hTranslationLength (hSLIsometry f)=2*dist u v := by
  obtain ⟨q,k,hk,hk1,haxis,hT,hact⟩ := hHyperbolicAxis_normalizer f hf ht
  let a := (q•v).im/Real.sqrt k
  have ha : 0<a := div_pos (q•v).im_pos (Real.sqrt_pos.mpr hk)
  have hv0 : (q•v).re=0 := by rw [haxis] at hv;exact hv
  have hb : Real.sqrt k*a=(q•v).im := by dsimp only [a];field_simp [(Real.sqrt_pos.mpr hk).ne']
  let p := metricProbe 0 a ha
  let r := metricProbe 0 (Real.sqrt k*a) (mul_pos (Real.sqrt_pos.mpr hk) ha)
  have hpr : r=q•v := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hv0.symm
    · exact hb
  have hvp : q⁻¹•r=v := by rw [hpr,inv_smul_smul]
  let u := q⁻¹•p
  have hu : u∈(hHyperbolicAxis f hf ht).carrier := by
    rw [haxis]
    change (q•(q⁻¹•p)).re=0
    rw [smul_inv_smul]
    rfl
  have hfact := realSL_halfturn_family_of_normalizer f q k hk hact a ha
  change HasHalfTurnFactorization f u (q⁻¹•r) at hfact
  rw [hvp] at hfact
  have hd : dist u v=dist p r := by
    have hh := (realGL_isometry (Matrix.SpecialLinearGroup.mapGL ℝ q)).dist_eq u v
    change dist (q•u) (q•v)=dist u v at hh
    dsimp only [u] at hh
    rw [smul_inv_smul,←hpr] at hh
    exact hh.symm
  have hlength : hTranslationLength (hSLIsometry f)=2*dist u v := by
    rw [hT,hd]
    exact (axis_halfturn_twice_centers_dist k a hk ha).symm
  exact ⟨u,⟨hu,hfact,hlength⟩,fun w hw =>halfTurnFactorization_first_unique f w u v hw.2.1 hfact⟩

/-- Transport the endpoint value across equality of both actual ray endpoints. -/
theorem hRayThrough_idealEndpoint_congr {v w v' w' : ℍ} (h : v≠w) (h' : v'≠w')
    (hv : v=v') (hw : w=w') :
    (hRayThrough v w h).idealEndpoint=(hRayThrough v' w' h').idealEndpoint := by
  subst v'
  subst w'
  rfl

/-- The ray from the first center through its half-turn partner ends at the genuine
attractive fixed point of the original hyperbolic Mobius transformation. -/
theorem realSL_hyperbolic_halfturn_ray_attractive (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) (ht : 4<(Matrix.trace f.val)^2) (v w : ℍ) (hne : v≠w)
    (hv : v∈(hHyperbolicAxis f hf ht).carrier) (h : HasHalfTurnFactorization f v w) :
    Mobius.MobiusAttractiveFixedPoint (realSLMobius f) (hRayThrough v w hne).idealEndpoint := by
  obtain ⟨q,k,hk,hk1,hn,hact⟩ := realSLMobius_hyperbolic_normalizer f hf ht
  have haxis := hHyperbolicAxis_normalizer_carrier f hf ht q k hk hk1 hn
  let a := (q•v).im
  have ha : 0<a := (q•v).im_pos
  have hv0 : (q•v).re=0 := by rw [haxis] at hv;exact hv
  let p := metricProbe 0 a ha
  let r := metricProbe 0 (Real.sqrt k*a) (mul_pos (Real.sqrt_pos.mpr hk) ha)
  have hp : p=q•v := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hv0.symm
    · rfl
  have hvp : q⁻¹•p=v := by rw [hp,inv_smul_smul]
  have hfamily := realSL_halfturn_family_of_normalizer f q k hk hact a ha
  change HasHalfTurnFactorization f (q⁻¹•p) (q⁻¹•r) at hfamily
  rw [hvp] at hfamily
  have hwp : w=q⁻¹•r := halfTurnFactorization_partner_unique f v w (q⁻¹•r) h hfamily
  let g := Matrix.SpecialLinearGroup.mapGL ℝ q⁻¹
  have hg : 0<g.val.det := by change 0<(q⁻¹).val.det;rw [(q⁻¹).det_coe];norm_num
  have hgp : g•p=v := hvp
  have hgr : g•r=w := hwp.symm
  let hpr := halfTurn_axis_height_ne a k ha hk hk1
  have hEnd := (hRayThrough p r hpr).realGLMap_idealEndpoint g hg
  rw [hRayThrough_realGLMap] at hEnd
  have hEnd' : (hRayThrough v w hne).idealEndpoint=
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (hRayThrough p r hpr).idealEndpoint := by
    exact (hRayThrough_idealEndpoint_congr ((realGL_isometry g).injective.ne hpr) hne hgp hgr).symm.trans hEnd
  rw [halfTurn_axis_ray_idealEndpoint a k ha hk hk1] at hEnd'
  have hkC : (positiveScalingUnit k hk:ℂ)≠1 := by change (k:ℂ)≠1;exact_mod_cast hk1
  change realSLMobius (q*f*q⁻¹)=Mobius.mobiusScaling (positiveScalingUnit k hk) at hn
  rw [DiscreteGroups.mobiusScaling_eq_standard _ hkC,map_mul,map_mul,map_inv] at hn
  have hconj : (realSLMobius q⁻¹)*Mobius.mobiusStandardElement (positiveScalingUnit k hk)*(realSLMobius q⁻¹)⁻¹=
      realSLMobius f := by
    rw [map_inv,inv_inv,←hn]
    group
  have hpair := (positiveScaling_attracting_repelling k hk hk1).conjugation (realSLMobius q⁻¹)
  rw [hconj] at hpair
  have hfrac : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)=(realSLMobius q⁻¹).val := by
    symm
    rw [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,realSLMobius_matrix]
  rw [hEnd',hfrac]
  exact ⟨_,hpair⟩

end LowDimensionalTopology.Geometry.Hyperbolic
