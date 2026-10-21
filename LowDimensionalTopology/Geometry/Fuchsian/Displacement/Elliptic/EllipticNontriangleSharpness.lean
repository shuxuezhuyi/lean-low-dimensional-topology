/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.FuchsianDisplacementInvariants
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticNontriangleFamilies
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.OneIdealTriangleDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.NonTriangleSharpness
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticMinimizers
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeDisplacementSharpness
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.WeakDisplacementGap
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleAxisExample
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.PureHyperbolicSharpness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane OnePoint Pointwise MatrixGroups ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
def sharpEllipticRightCenter (n : ℕ) (hn : 2≤n) : ℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (sharpEllipticCos n) (sharpEllipticSin
    n) (sharpEllipticSin_pos n hn)

def sharpEllipticLeftCenter (n : ℕ) (hn : 2≤n) (t : ℝ) : ℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-sharpEllipticCos n-t) (sharpEllipticSin
    n) (sharpEllipticSin_pos n hn)

theorem sharpEllipticRightCenter_norm (n : ℕ) (hn : 2≤n) :
    ‖(sharpEllipticRightCenter n hn:ℂ)‖=1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
  rw [←Complex.normSq_eq_norm_sq]
  norm_num [sharpEllipticRightCenter,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply]
  nlinarith [sharpElliptic_trig n]

theorem sharpEllipticRightCenter_fixed (n : ℕ) (hn : 2≤n) :
    standardHeckeCornerSL n • sharpEllipticRightCenter n hn=sharpEllipticRightCenter n hn := by
  have h:=translation_inversion_fixed_unit _ (sharpEllipticRightCenter_norm n hn)
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*sharpEllipticCos n)*modularInversionSL))
    (sharpEllipticRightCenter n hn)=_
  rw [map_mul]
  exact h

theorem sharpEllipticRightCenter_canonical (n : ℕ) (hn : 2≤n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter (standardHeckeCornerSL n)
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ (sharpEllipticCorner_elliptic n
        hn).1).mp
        (sharpEllipticCorner_elliptic n hn))=sharpEllipticRightCenter n hn :=
  ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff _ _ _).mp (sharpEllipticRightCenter_fixed n
    hn)).symm

theorem sharpEllipticCorner_half_sine (n : ℕ) (hn : 2≤n) :
    Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle (standardHeckeCornerSL n)
      (sharpEllipticCorner_elliptic n hn)/2)=
      sharpEllipticSin n := by
  rw [elliptic_actual_angle_height,sharpEllipticRightCenter_canonical n hn]
  have hc : standardHeckeCornerSL n 1 0=1:=by
    norm_num [standardHeckeCornerSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,Matrix.mul_apply,Fin.sum_univ_two]
  rw [hc,abs_one,one_mul]
  rfl

theorem sharpEllipticCorner_radial (n : ℕ) (hn : 2≤n) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL n)) z=
      sharpEllipticSin n*Real.sinh (dist (sharpEllipticRightCenter n hn) z) := by
  have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_actual_angle_radial (standardHeckeCornerSL
    n) (sharpEllipticCorner_elliptic n hn) z
  rw [sharpEllipticCorner_half_sine n hn,sharpEllipticRightCenter_canonical n hn] at h
  exact h

theorem sharpEllipticMirror_center (n : ℕ) (hn : 2≤n) (t : ℝ) :
    sharpEllipticMirror t (sharpEllipticRightCenter n hn)=sharpEllipticLeftCenter n hn t := by
  apply UpperHalfPlane.ext
  rw [sharpEllipticMirror_coe]
  apply Complex.ext <;>
    simp [sharpEllipticRightCenter,sharpEllipticLeftCenter,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]

theorem sharpEllipticLeft_radial (n : ℕ) (hn : 2≤n) (t : ℝ) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpEllipticLeftSL n t)) z=
      sharpEllipticSin n*Real.sinh (dist (sharpEllipticLeftCenter n hn t) z) := by
  let C:=sharpEllipticMirror t
  let g:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL n)
  have hc : ((C.symm.trans g).trans
    C)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpEllipticLeftSL n t):=
    sharpEllipticLeftConjugation_corner n t
  have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement_conjugation g C (C z)
  rw [hc,sharpEllipticMirror_involutive] at h
  rw [sharpEllipticCorner_radial n hn] at h
  have hd:=C.dist_eq (sharpEllipticRightCenter n hn) (C z)
  rw [sharpEllipticMirror_involutive,sharpEllipticMirror_center] at hd
  rw [←hd] at h
  exact h

def sharpEllipticCosh (p q : ℕ) (t : ℝ) : ℝ :=
  (1+sharpEllipticCos p*sharpEllipticCos q+(sharpEllipticCos p+sharpEllipticCos q)*t+t^2/2)/
    (sharpEllipticSin p*sharpEllipticSin q)

theorem sharpElliptic_centers_cosh (p q : ℕ) (hp : 2≤p) (hq : 2≤q) (t : ℝ) :
    Real.cosh (dist (sharpEllipticLeftCenter p hp t) (sharpEllipticRightCenter q hq))=
      sharpEllipticCosh p q t := by
  rw [UpperHalfPlane.cosh_dist']
  change ((-sharpEllipticCos p-t-sharpEllipticCos q)^2+(sharpEllipticSin p)^2+
    (sharpEllipticSin q)^2)/(2*sharpEllipticSin p*sharpEllipticSin q)=_
  unfold sharpEllipticCosh
  field_simp [(sharpEllipticSin_pos p hp).ne',(sharpEllipticSin_pos q hq).ne']
  nlinarith [sharpElliptic_trig p,sharpElliptic_trig q]

/-- The genuine all-half-plane displacement infimum of this actual elliptic family. -/
theorem sharpElliptic_displacementM_square (p q : ℕ) (hp : 2≤p) (hq : 2≤q) (t : ℝ) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpEllipticLeftSL p t))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL q)))^2=
      (sharpEllipticSin p)^2*(sharpEllipticSin q)^2*((sharpEllipticCosh p q t)^2-1)/
        ((sharpEllipticSin p)^2+(sharpEllipticSin q)^2+
          2*sharpEllipticSin p*sharpEllipticSin q*sharpEllipticCosh p q t) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.radial_displacementM_square _ _ _ _ _ _ (sharpEllipticSin_pos p
    hp)
    (sharpEllipticSin_pos q hq) (sharpEllipticLeft_radial p hp t) (sharpEllipticCorner_radial q hq),
    Real.sinh_sq,sharpElliptic_centers_cosh p q hp hq t]

def sharpEllipticRatio (p q : ℕ) (t : ℝ) : ℝ :=
  (sharpEllipticSin p)^2*(sharpEllipticSin q)^2*((sharpEllipticCosh p q t)^2-1)/
    ((sharpEllipticSin p)^2+(sharpEllipticSin q)^2+
      2*sharpEllipticSin p*sharpEllipticSin q*sharpEllipticCosh p q t)

def sharpEllipticM (p q : ℕ) (t : ℝ) : ℝ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpEllipticLeftSL p t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL q))

def sharpEllipticSourceBound (p q : ℕ) : ℝ :=
  Real.sqrt ((sharpEllipticCos p+sharpEllipticCos q)^2/
    (4-(sharpEllipticCos p-sharpEllipticCos q)^2))

theorem sharpEllipticM_sqrt (p q : ℕ) (hp : 2≤p) (hq : 2≤q) (t : ℝ) :
    sharpEllipticM p q t=Real.sqrt (sharpEllipticRatio p q t) := by
  calc
    sharpEllipticM p q t=Real.sqrt ((sharpEllipticM p q t)^2):=
      (Real.sqrt_sq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _)).symm
    _=Real.sqrt (sharpEllipticRatio p q t):=
      congrArg Real.sqrt (sharpElliptic_displacementM_square p q hp hq t)

theorem sharpElliptic_ratio_scalar (s t c d : ℝ) (hs : 0<s) (ht : 0<t)
    (hsc : s^2+c^2=1) (htd : t^2+d^2=1) :
    s^2*t^2*(((1+c*d)/(s*t))^2-1)/(s^2+t^2+2*s*t*((1+c*d)/(s*t)))=
      (c+d)^2/(4-(c-d)^2) := by
  have hst : s*t≠0:=mul_ne_zero hs.ne' ht.ne'
  have hfrac : (s*t)^2*((1+c*d)/(s*t))^2=(1+c*d)^2:=by field_simp
  have hcancel : 2*s*t*((1+c*d)/(s*t))=2*(1+c*d):=by field_simp
  have hden : s^2+t^2+2*s*t*((1+c*d)/(s*t))=4-(c-d)^2:=by
    rw [hcancel]
    nlinarith
  have hnum : s^2*t^2*(((1+c*d)/(s*t))^2-1)=(c+d)^2:=by
    calc
      _=(s*t)^2*((1+c*d)/(s*t))^2-(s*t)^2:=by ring
      _=(1+c*d)^2-(s*t)^2:=by rw [hfrac]
      _=(c+d)^2:=by
        have hs₂ : s^2=1-c^2:=by linarith
        have ht₂ : t^2=1-d^2:=by linarith
        rw [mul_pow,hs₂,ht₂]
        ring
  rw [hnum,hden]

theorem sharpEllipticM_zero (p q : ℕ) (hp : 2≤p) (hq : 2≤q) :
    sharpEllipticM p q 0=sharpEllipticSourceBound p q := by
  rw [sharpEllipticM_sqrt p q hp hq]
  apply congrArg Real.sqrt
  simpa only [sharpEllipticRatio,sharpEllipticCosh,sharpEllipticSourceBound,
    mul_zero,zero_pow (by decide : (2:ℕ)≠0),zero_div,add_zero] using
    sharpElliptic_ratio_scalar _ _ _ _ (sharpEllipticSin_pos p hp) (sharpEllipticSin_pos q hq)
      (sharpElliptic_trig p) (sharpElliptic_trig q)

theorem sharpEllipticCosh_continuous (p q : ℕ) : Continuous (sharpEllipticCosh p q) := by
  unfold sharpEllipticCosh
  fun_prop

theorem sharpEllipticM_continuousAt_zero (p q : ℕ) (hp : 2≤p) (hq : 2≤q) :
    ContinuousAt (sharpEllipticM p q) 0 := by
  have hc : 0<sharpEllipticCosh p q 0:=by
    rw [←sharpElliptic_centers_cosh p q hp hq 0]
    exact Real.cosh_pos _
  have hd : 0<(sharpEllipticSin p)^2+(sharpEllipticSin q)^2+
      2*sharpEllipticSin p*sharpEllipticSin q*sharpEllipticCosh p q 0:=by
    have hs:=sharpEllipticSin_pos p hp
    have ht:=sharpEllipticSin_pos q hq
    positivity
  have hC:=sharpEllipticCosh_continuous p q
  have hnum : Continuous (fun t : ℝ=>(sharpEllipticSin p)^2*(sharpEllipticSin q)^2*
      ((sharpEllipticCosh p q t)^2-1)):=by fun_prop
  have hden : Continuous (fun t : ℝ=>(sharpEllipticSin p)^2+(sharpEllipticSin q)^2+
      2*sharpEllipticSin p*sharpEllipticSin q*sharpEllipticCosh p q t):=by fun_prop
  have hr : ContinuousAt (sharpEllipticRatio p q) 0:=
    hnum.continuousAt.div hden.continuousAt hd.ne'
  have he : sharpEllipticM p q=(fun t=>Real.sqrt (sharpEllipticRatio p q t)):=
    funext (sharpEllipticM_sqrt p q hp hq)
  rw [he]
  exact Real.continuous_sqrt.continuousAt.comp hr

theorem sharpEllipticM_tendsto (p q : ℕ) (hp : 2≤p) (hq : 2≤q) :
    Tendsto (sharpEllipticM p q) (𝓝[>] (0:ℝ)) (𝓝 (sharpEllipticSourceBound p q)) := by
  have h:=(sharpEllipticM_continuousAt_zero p q hp hq).tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 (0:ℝ))
  rwa [sharpEllipticM_zero p q hp hq] at h

theorem sharpElliptic_center_distance_continuous (p q : ℕ) (hp : 2≤p) (hq : 2≤q) :
    Continuous (fun t=>dist (sharpEllipticLeftCenter p hp t) (sharpEllipticRightCenter q hq)) := by
  have h : Continuous (sharpEllipticLeftCenter p hp):=by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun t : ℝ=>(⟨-sharpEllipticCos p-t,sharpEllipticSin p⟩:ℂ))
    simp_rw [Complex.mk_eq_add_mul_I]
    fun_prop
  exact h.dist continuous_const

theorem sharpElliptic_center_distance_strictMono (p q : ℕ) (hp : 2≤p) (hq : 2≤q) :
    StrictMonoOn (fun t=>dist (sharpEllipticLeftCenter p hp t) (sharpEllipticRightCenter q hq)) (Ici 0) := by
  intro a ha b hb hab
  change 0≤a at ha
  change 0≤b at hb
  have hcosh : sharpEllipticCosh p q a<sharpEllipticCosh p q b:=by
    unfold sharpEllipticCosh
    rw [div_lt_div_iff_of_pos_right (mul_pos (sharpEllipticSin_pos p hp) (sharpEllipticSin_pos q hq))]
    have hinc:=mul_nonneg (add_nonneg (sharpEllipticCos_nonneg p hp) (sharpEllipticCos_nonneg q hq))
      (sub_nonneg.mpr hab.le)
    have hsquare:=mul_pos (sub_pos.mpr hab) (by linarith [ha] : 0<b+a)
    nlinarith
  rw [←sharpElliptic_centers_cosh p q hp hq a,←sharpElliptic_centers_cosh p q hp hq b,
    Real.cosh_lt_cosh,abs_of_nonneg dist_nonneg,abs_of_nonneg dist_nonneg] at hcosh
  exact hcosh

theorem sharpElliptic_approaches_source (p q : ℕ) (hp : 2≤p) (hq : 2≤q)
    (ε : ℝ) (hε : 0<ε) :
    ∃t : ℝ,0<t ∧ sharpEllipticM p q t<sharpEllipticSourceBound p q+ε := by
  have he : ∀ᶠt in 𝓝 (0:ℝ),sharpEllipticM p q t<sharpEllipticSourceBound p q+ε:=by
    have htarget : ∀ᶠy in 𝓝 (sharpEllipticM p q 0),y<sharpEllipticSourceBound p q+ε:=by
      rw [sharpEllipticM_zero p q hp hq]
      exact eventually_lt_nhds (by linarith)
    exact (sharpEllipticM_continuousAt_zero p q hp hq).tendsto.eventually htarget
  obtain ⟨δ,hδ,hball⟩:=Metric.eventually_nhds_iff.mp he
  refine ⟨δ/2,by linarith,hball ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_pos (by linarith : 0<δ/2)]
  linarith

/-- The actual limiting center distance has the stated parabolic threshold. -/
theorem sharpElliptic_threshold_cosh (p q : ℕ) (hp : 2≤p) (hq : 2≤q) :
    Real.cosh (dist (sharpEllipticLeftCenter p hp 0) (sharpEllipticRightCenter q hq))=
      (1+sharpEllipticCos p*sharpEllipticCos q)/(sharpEllipticSin p*sharpEllipticSin q) := by
  simpa [sharpEllipticCosh] using sharpElliptic_centers_cosh p q hp hq 0

/-- Every positive parameter lies strictly beyond the actual limiting distance. -/
theorem sharpElliptic_center_distance_above (p q : ℕ) (hp : 2≤p) (hq : 2≤q)
    (t : ℝ) (ht : 0<t) :
    dist (sharpEllipticLeftCenter p hp 0) (sharpEllipticRightCenter q hq)<
      dist (sharpEllipticLeftCenter p hp t) (sharpEllipticRightCenter q hq) :=
  sharpElliptic_center_distance_strictMono p q hp hq (by simp) ht.le ht

/-- The genuine center distances approach that threshold from above. -/
theorem sharpElliptic_center_distance_tendsto (p q : ℕ) (hp : 2≤p) (hq : 2≤q) :
    Tendsto (fun t=>dist (sharpEllipticLeftCenter p hp t) (sharpEllipticRightCenter q hq))
      (𝓝[>] (0:ℝ)) (𝓝 (dist (sharpEllipticLeftCenter p hp 0) (sharpEllipticRightCenter q hq))) :=
  (sharpElliptic_center_distance_continuous p q hp hq).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds

/-- The order-(2,3) specialization is the universal nontriangle constant. -/
theorem sharpEllipticSourceBound_two_three : sharpEllipticSourceBound 2 3=1/Real.sqrt 15 := by
  norm_num [sharpEllipticSourceBound,sharpEllipticCos,Real.cos_pi_div_two,Real.cos_pi_div_three]

/-- Original full-disc displacement agrees with the actual real lifts in the
literal half-plane chart; the chosen normalizer is immaterial. -/
theorem halfPlane_realSL_displacementM {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (f g : H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=f.val) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B=g.val) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM P.asFuchsianDisc f g=_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  let D:=P.asFuchsianDisc
  have h1 : (1:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup).val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    change (fun x : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex=>x) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    exact image_id _
  let F:=geometricHalfPlaneChart D 1 h1
  have hpoint (a : H) (C : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hC :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C=a.val)
      (x : (fuchsianGeometricDomain D).carrier) :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.sinhDisplacement D a x=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C) (F x) := by
    have hact : F (a • x)=C • F x:=by
      apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
      change _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (geometricHalfPlaneChart D 1 h1 (a •
        x))=
        _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (C • geometricHalfPlaneChart D 1 h1 x)
      change (((geometricHalfPlaneChart D 1 h1 (a •
        x):ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
        (((C • geometricHalfPlaneChart D 1 h1 x:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,geometricHalfPlaneChart_extended,geometricHalfPlaneChart_extended,hC]
      rfl
    unfold _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.sinhDisplacement
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist_eq_chart D 1 h1,hact]
    rfl
  change _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D f g=_
  unfold _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
  simp_rw [hpoint f A hA,hpoint g B hB]
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨F x,rfl⟩
  · rintro ⟨y,rfl⟩
    obtain ⟨x,rfl⟩:=F.surjective y
    exact ⟨x,rfl⟩

/--
Best possibility of the order-sensitive nontriangle bound.
All group, order, domain, discreteness and nontriangle facts are constructed.
-/
theorem nontriangle_elliptic_pair_order_displacement_bound_sharp (p q : ℕ) (hp : 2≤p) (hq : 2≤q)
    (hpq : p≠2 ∨ q≠2) (ε : ℝ) (hε : 0<ε) :
    ∃H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∃D : FuchsianDisc H,∃f g : H,
      Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)=H ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H ∧ ¬IsMobiusTriangleGroup H ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val ∧ orderOf f.val=p ∧ orderOf g.val=q ∧
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D f g<Real.sqrt
        ((Real.cos (Real.pi/(p:ℝ))+Real.cos (Real.pi/(q:ℝ)))^2/
          (4-(Real.cos (Real.pi/(p:ℝ))-Real.cos (Real.pi/(q:ℝ)))^2))+ε := by
  obtain ⟨t,ht,hM⟩:=sharpElliptic_approaches_source p q hp hq ε hε
  let H:=sharpEllipticMobiusGroup p q t
  let P:=sharpEllipticMobiusData p q hp hq t ht
  let f : H:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpEllipticLeftSL p
    t),sharpEllipticLeft_mem p q t⟩
  let g : H:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (standardHeckeCornerSL
    q),sharpEllipticRight_mem p q t⟩
  refine ⟨H,P.asFuchsianDisc,f,g,(sharpEllipticMobiusGroup_generators p q t).symm,
    sharpEllipticMobiusGroup_nonElementary p q hp hq hpq t ht,
    sharpEllipticMobiusGroup_not_triangle p q hp hq hpq t ht,
    sharpEllipticLeft_elliptic p hp t,sharpEllipticCorner_elliptic q hq,
    sharpEllipticLeft_order p hp t,sharpEllipticCorner_order q hq,?_⟩
  rw [halfPlane_realSL_displacementM P f g _ _ rfl rfl]
  exact hM

/-- The nontriangle universal value is approached by actual order-(2,3) pairs. -/
theorem nontriangle_order_two_three_pair_uniform_displacement_bound_sharp (ε : ℝ) (hε : 0<ε) :
    ∃H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∃D : FuchsianDisc H,∃f g : H,
      Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)=H ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H ∧ ¬IsMobiusTriangleGroup H ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val ∧ orderOf f.val=2 ∧ orderOf g.val=3 ∧
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D f g<1/Real.sqrt 15+ε := by
  obtain ⟨H,D,f,g,hgen,hne,hnt,hf,hg,hof,hog,hM⟩:=
    nontriangle_elliptic_pair_order_displacement_bound_sharp 2 3 (by decide) (by decide) (by decide) ε hε
  refine ⟨H,D,f,g,hgen,hne,hnt,hf,hg,hof,hog,?_⟩
  change _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D f g<sharpEllipticSourceBound 2 3+ε at hM
  rwa [sharpEllipticSourceBound_two_three] at hM

end LowDimensionalTopology.Geometry.Fuchsian
