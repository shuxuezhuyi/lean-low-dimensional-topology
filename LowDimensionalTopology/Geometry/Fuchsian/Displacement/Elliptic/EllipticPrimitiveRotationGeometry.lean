/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.NonEllipticMaximumDisplacement
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.CollinearHalfTurns
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HorocyclicRegions
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveEllipticAngles
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.EllipticProducts
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.AngleParallelism
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.AngularMeasure
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticCenterMinimum
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.CommutatorGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPairReflectionGroups
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleAngleSum
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticRotationAngles
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.MobiusTriangleGroups
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleSupergroups
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPairSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticTriangleDisplacementSharpness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleIntegralDiscreteness
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticMinimizers
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set InnerProductGeometry
open scoped UpperHalfPlane MatrixGroups OnePoint Pointwise ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem complex_rotation_step_improves_real_part (z : ℂ) (θ : ℝ)
    (hθ : 0 < θ) (hθπ : θ ≤ Real.pi)
    (hgap : z.re < ‖z‖ * Real.cos (θ / 2)) :
    z.re < (Complex.exp ((θ : ℂ) * Complex.I) * z).re ∨
      z.re < (Complex.exp ((-θ : ℝ) * Complex.I) * z).re := by
  let s := Real.sin (θ / 2)
  let c := Real.cos (θ / 2)
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hc : 0 ≤ c := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcircle : s^2 + c^2 = 1 := Real.sin_sq_add_cos_sq (θ / 2)
  have hnorm : ‖z‖^2 = z.re^2 + z.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hcore : z.re * s < |z.im| * c := by
    by_cases hr : 0 ≤ z.re
    · have hsq : z.re^2 < (‖z‖ * c)^2 :=
        (sq_lt_sq₀ hr (mul_nonneg (norm_nonneg z) hc)).mpr hgap
      have hunit := congrArg (fun x : ℝ => z.re^2 * x) hcircle
      have hdiff : (z.re * s)^2 < (|z.im| * c)^2 := by
        rw [mul_pow, hnorm] at hsq
        simp only [mul_pow, sq_abs]
        nlinarith only [hsq, hunit]
      exact (sq_lt_sq₀ (mul_nonneg hr hs.le) (mul_nonneg (abs_nonneg _) hc)).mp hdiff
    · have hneg : z.re * s < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hr) hs
      exact hneg.trans_le (mul_nonneg (abs_nonneg _) hc)
  have hgain : z.re < z.re * Real.cos θ + |z.im| * Real.sin θ := by
    have hpos := mul_pos (show 0 < 2 * s by positivity) (sub_pos.mpr hcore)
    have hunit := congrArg (fun x : ℝ => z.re * x) hcircle
    have hsin : Real.sin θ = 2 * s * c := by
      simpa only [show 2 * (θ / 2) = θ by ring] using Real.sin_two_mul (θ / 2)
    have hcos : Real.cos θ = 2 * c^2 - 1 := by
      simpa only [show 2 * (θ / 2) = θ by ring] using Real.cos_two_mul (θ / 2)
    rw [hsin, hcos]
    nlinarith only [hpos, hunit]
  by_cases hi : 0 ≤ z.im
  · right
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Real.cos_neg, Real.sin_neg]
    rw [abs_of_nonneg hi] at hgain
    nlinarith only [hgain]
  · left
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rw [abs_of_neg (lt_of_not_ge hi)] at hgain
    nlinarith only [hgain]

theorem complex_rotation_step_decreases_distance (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) (hangle : θ / 2 < angle u v) :
    ‖u - Complex.exp ((θ : ℂ) * Complex.I) * v‖ < ‖u - v‖ ∨
      ‖u - Complex.exp ((-θ : ℝ) * Complex.I) * v‖ < ‖u - v‖ := by
  let z := v * conj u
  have hnorm : ‖z‖ = ‖u‖ * ‖v‖ := by simp only [z, norm_mul, Complex.norm_conj, mul_comm]
  have hcos : Real.cos (angle u v) < Real.cos (θ / 2) :=
    Real.strictAntiOn_cos ⟨by linarith, by linarith⟩
      ⟨angle_nonneg u v, angle_le_pi u v⟩ hangle
  have hprod : 0 < ‖u‖ * ‖v‖ := mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
  have hinner : Real.cos (angle u v) * (‖u‖ * ‖v‖) = z.re := by
    rw [cos_angle_mul_norm_mul_norm, Complex.inner]
  have hgap : z.re < ‖z‖ * Real.cos (θ / 2) := by
    rw [hnorm, ← hinner]
    nlinarith only [mul_lt_mul_of_pos_right hcos hprod]
  have hdist (α : ℝ) : ‖u - Complex.exp ((α : ℂ) * Complex.I) * v‖^2 =
      ‖u‖^2 + ‖v‖^2 - 2 * (Complex.exp ((α : ℂ) * Complex.I) * z).re := by
    rw [norm_sub_sq_real, Complex.inner, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    simp only [z, mul_assoc]
    ring
  have hdist0 : ‖u - v‖^2 = ‖u‖^2 + ‖v‖^2 - 2 * z.re := by
    rw [norm_sub_sq_real, Complex.inner]
    ring
  rcases complex_rotation_step_improves_real_part z θ hθ hθπ hgap with h | h
  · left
    apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith only [hdist θ, hdist0, h]
  · right
    apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith only [hdist (-θ), hdist0, h]

theorem disc_rotation_step_decreases_distance (u v : 𝔻)
    (hu : (u : ℂ) ≠ 0) (hv : (v : ℂ) ≠ 0)
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi)
    (hangle : θ / 2 < angle (u : ℂ) (v : ℂ)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist u (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation (Complex.exp ((θ : ℂ) * Complex.I))
      (Complex.norm_exp_ofReal_mul_I θ) v) < _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist u v ∨
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist u (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation (Complex.exp ((-θ : ℝ) * Complex.I))
      (Complex.norm_exp_ofReal_mul_I (-θ)) v) < _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist u v := by
  have hcompare (q : ℂ) (hq : ‖q‖ = 1) (hh : ‖(u : ℂ) - q * v‖ < ‖(u : ℂ) - v‖) :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist u (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation q hq v) < _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist u v := by
    have hden : 0 < (1 - ‖(u : ℂ)‖^2) * (1 - ‖(v : ℂ)‖^2) :=
      mul_pos (sub_pos.mpr u.sq_norm_lt_one) (sub_pos.mpr v.sq_norm_lt_one)
    have hsq := (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hh
    have hc : Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist u
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation q hq v)) <
        Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist u v) := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_cosh_distance,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_cosh_distance,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation_coe, norm_mul, hq, one_mul]
      linarith only [div_lt_div_of_pos_right
        (mul_lt_mul_of_pos_left hsq (by norm_num : (0 : ℝ) < 2)) hden]
    have hp : 0 ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist u (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation q hq v) := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]
      exact dist_nonneg
    have hp' : 0 ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist u v := by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]; exact dist_nonneg
    simpa only [abs_of_nonneg hp, abs_of_nonneg hp'] using Real.cosh_lt_cosh.mp hc
  rcases complex_rotation_step_decreases_distance (u : ℂ) (v : ℂ) hu hv θ hθ hθπ hangle with h | h
  · exact Or.inl (hcompare _ (Complex.norm_exp_ofReal_mul_I θ) h)
  · exact Or.inr (hcompare _ (Complex.norm_exp_ofReal_mul_I (-θ)) h)

theorem disc_minimal_rotation_angle_dichotomy (u v : 𝔻)
    (hu : (u : ℂ) ≠ 0) (hv : (v : ℂ) ≠ 0)
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi)
    (hmin : ∀ w ∈ ({(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation (Complex.exp ((θ : ℂ) *
      Complex.I))
      (Complex.norm_exp_ofReal_mul_I θ) v),
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation (Complex.exp ((-θ : ℝ) * Complex.I))
        (Complex.norm_exp_ofReal_mul_I (-θ)) v)} : Set 𝔻),
      w ≠ u → _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist u v ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist u w) :
    angle (u : ℂ) (v : ℂ) ≤ θ / 2 ∨
      (angle (u : ℂ) (v : ℂ) = θ ∧ ‖(u : ℂ)‖ = ‖(v : ℂ)‖) := by
  have hcollision (q : ℂ) (hq : ‖q‖ = 1) (hqr : q.re = Real.cos θ)
      (he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation q hq v = u) :
      angle (u : ℂ) (v : ℂ) = θ ∧ ‖(u : ℂ)‖ = ‖(v : ℂ)‖ := by
    have hval : (u : ℂ) = q * v := (congrArg (fun z : 𝔻 => (z : ℂ)) he).symm
    have hinner : (((v : ℂ) * conj (q * v))).re = q.re * ‖(v : ℂ)‖^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    have hangle : angle (u : ℂ) (v : ℂ) = θ := by
      apply Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨hθ.le, hθπ⟩
      have hi := cos_angle_mul_norm_mul_norm (u : ℂ) (v : ℂ)
      rw [Complex.inner, hval, norm_mul, hq, one_mul, hinner, hqr] at hi
      have hn : 0 < ‖(v : ℂ)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
      rw [hval]
      nlinarith only [hi, hn]
    exact ⟨hangle, by rw [hval, norm_mul, hq, one_mul]⟩
  by_cases hang : angle (u : ℂ) (v : ℂ) ≤ θ / 2
  · exact Or.inl hang
  · right
    rcases disc_rotation_step_decreases_distance u v hu hv θ hθ hθπ (lt_of_not_ge hang) with h | h
    · have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation (Complex.exp ((θ : ℂ) * Complex.I))
          (Complex.norm_exp_ofReal_mul_I θ) v = u := by
        by_contra hn
        exact not_lt_of_ge (hmin _ (by simp) hn) h
      exact hcollision _ (Complex.norm_exp_ofReal_mul_I θ) (Complex.exp_ofReal_mul_I_re θ) he
    · have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation (Complex.exp ((-θ : ℝ) * Complex.I))
          (Complex.norm_exp_ofReal_mul_I (-θ)) v = u := by
        by_contra hn
        exact not_lt_of_ge (hmin _ (by simp) hn) h
      exact hcollision _ (Complex.norm_exp_ofReal_mul_I (-θ))
        (by rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]) he



open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate Complex.UnitDisc

theorem least_elliptic_realSL_order_two_le (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hleast : HasLeastEllipticRotation
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    2≤orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
  have ht:=hleast.squaredTrace_order
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace] at ht
  have htR : (Matrix.trace A.val)^2=4*(Real.cos (Real.pi/orderOf
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)))^2 :=
    Complex.ofReal_injective ht
  have hn0 : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)≠0 := by
    intro hn
    rw [hn,Nat.cast_zero,div_zero,Real.cos_zero] at htR
    have hh:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA
    nlinarith only [htR,hh]
  have hn1 : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)≠1 := by
    intro hn
    exact hA.1 (orderOf_eq_one_iff.mp hn)
  omega

theorem least_elliptic_actual_angle (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hleast : HasLeastEllipticRotation
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA=2*Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∨
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA=2*Real.pi-2*Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
  let n:=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
  let θ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA
  have hn : 2≤n:=least_elliptic_realSL_order_two_le A hA hleast
  have hnR : (2:ℝ)≤n:=by exact_mod_cast hn
  have hnpos : (0:ℝ)<n:=by linarith only [hnR]
  have hβ0 : 0≤Real.pi/n:=div_nonneg Real.pi_pos.le hnpos.le
  have hβπ : Real.pi/n≤Real.pi/2:=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hnR
  have hθ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo A hA
  have ht:=hleast.squaredTrace_order
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace] at ht
  have htR : (Matrix.trace A.val)^2=4*(Real.cos (Real.pi/n))^2 :=
    Complex.ofReal_injective ht
  have hspec:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A hA).2.2.2
  have he : (Real.cos (θ/2))^2=(Real.cos (Real.pi/n))^2 := by
    nlinarith only [htR,hspec]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he|he
  · have hangle : θ/2=Real.pi/n:=Real.strictAntiOn_cos.injOn
      ⟨hθ.1.le,hθ.2.le⟩ ⟨hβ0,by linarith only [hβπ,Real.pi_pos]⟩ he
    left
    change θ=2*Real.pi/n
    linear_combination 2*hangle
  · have hangle : θ/2=Real.pi-Real.pi/n:=Real.strictAntiOn_cos.injOn
      ⟨hθ.1.le,hθ.2.le⟩ ⟨by linarith only [hβπ,Real.pi_pos],by linarith only [hβ0]⟩
      (by rw [Real.cos_pi_sub];exact he)
    right
    change θ=2*Real.pi-2*Real.pi/n
    linear_combination 2*hangle

theorem realSL_normalizer_multiplier_actual_angle
    (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (a b : ℝ) (hu : a^2+b^2=1)
    (hq : q•_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)=UpperHalfPlane.I)
    (hr : q*A*q⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL a b hu) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationMultiplier a b=Complex.exp (Complex.I*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA:ℂ)) := by
  let v:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  have hv : A•v=v:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ v).mpr rfl
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_rotation_derivative A q a b hu v hv hq
    hr).unique
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A hA).2.1

theorem least_elliptic_normalizer_multiplier
    (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hleast : HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (a b : ℝ) (hu
      : a^2+b^2=1)
    (hq : q•_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)=UpperHalfPlane.I)
    (hr : q*A*q⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL a b hu) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationMultiplier a b=Complex.exp (((2*Real.pi/orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):ℝ):ℂ)*Complex.I) ∨
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationMultiplier a b=Complex.exp (((-(2*Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)):ℝ):ℂ)*Complex.I) := by
  rw [realSL_normalizer_multiplier_actual_angle A q hA a b hu hq hr]
  rcases least_elliptic_actual_angle A hA hleast with hθ|hθ
  · left
    rw [hθ,mul_comm]
  · right
    rw [hθ]
    have he : Complex.I*((2*Real.pi-2*Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A):ℝ):ℂ)=
        2*Real.pi*Complex.I+((-(2*Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)):ℝ):ℂ)*Complex.I := by
      push_cast
      ring
    rw [he,Complex.exp_add,Complex.exp_two_pi_mul_I,one_mul]

theorem least_elliptic_normalizer_disc_action
    (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hleast : HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (a b : ℝ) (hu
      : a^2+b^2=1)
    (hq : q•_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)=UpperHalfPlane.I)
    (hr : q*A*q⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL a b hu) :
    (∀z : 𝔻,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL a b hu) z:ℂ)=
      Complex.exp (((2*Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        A):ℝ):ℂ)*Complex.I)*(z:ℂ)) ∨
    (∀z : 𝔻,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL a b hu) z:ℂ)=
      Complex.exp (((-(2*Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)):ℝ):ℂ)*Complex.I)*(z:ℂ)) := by
  rcases least_elliptic_normalizer_multiplier A q hA hleast a b hu hq hr with hm|hm
  · left
    intro z
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL_disc_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation_coe,hm]
  · right
    intro z
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL_disc_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation_coe,hm]

theorem least_elliptic_actual_sin_half (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hleast : HasLeastEllipticRotation
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA/2)=Real.sin (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) := by
  rcases least_elliptic_actual_angle A hA hleast with hθ|hθ
  · rw [hθ,show (2*Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))/2=
      Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) by ring]
  · rw [hθ,show (2*Real.pi-2*Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))/2=
      Real.pi-Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) by ring,Real.sin_pi_sub]

theorem least_elliptic_exists_normalized_disc_root
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hleast : HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    ∃(q : Matrix.SpecialLinearGroup (Fin 2) ℝ)(a b : ℝ)(hu : a^2+b^2=1),
      q•_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)=UpperHalfPlane.I ∧
      b≠0 ∧ q*A*q⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL a b hu ∧
      ((∀z : 𝔻,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL a b hu) z:ℂ)=
          Complex.exp (((2*Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
            A):ℝ):ℂ)*Complex.I)*(z:ℂ)) ∨
       (∀z : 𝔻,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action
         (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL a b hu) z:ℂ)=
          Complex.exp (((-(2*Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)):ℝ):ℂ)*Complex.I)*(z:ℂ))) := by
  obtain ⟨q,a,b,hu,hq,hb,hr⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_normal_form A hA
  exact ⟨q,a,b,hu,hq,hb,hr,least_elliptic_normalizer_disc_action A q hA hleast a b hu hq hr⟩



open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc

theorem rayThrough_angle_cayley_of_start_eq_I
    (w u v : ℍ) (hw : w=UpperHalfPlane.I) (hwu : w≠u) (hwv : w≠v) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w u hwu) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w v hwv)=
      angle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc u:ℂ) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc v:ℂ) := by
  subst w
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_I_cayley (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough UpperHalfPlane.I u hwu)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough UpperHalfPlane.I v hwv)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _
      _) hwu.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _ _) hwv.symm

theorem centered_disc_angle_eq_hInteriorAngleMeasure
    (q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w u v : ℍ)
    (hq : q•w=UpperHalfPlane.I) (hwu : w≠u) (hwv : w≠v) :
    angle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
      (q•u):ℂ) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (q•v):ℂ)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w u hwu) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w v hwv) := by
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ q
  have hqu : g•w≠g•u := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g).injective.ne hwu
  have hqv : g•w≠g•v := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g).injective.ne hwv
  have hm:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_realGLMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w u hwu) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w v hwv) g
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_realGLMap,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_realGLMap] at hm
  have h0:=rayThrough_angle_cayley_of_start_eq_I (g•w) (g•u) (g•v) hq hqu hqv
  exact h0.symm.trans hm


open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc

theorem least_elliptic_minimal_center_angle
    (C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hC : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)) (hleast : HasLeastEllipticRotation
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C))
    (u v : ℍ)
    (hwu : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC) ≠ u)
    (hwv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC) ≠ v)
    (hmin : ∀ D ∈ ({C, C⁻¹} : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)),
      D • v ≠ u → dist u v ≤ dist u (D • v)) :
    let w := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC)
    let γ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w u hwu) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w v hwv)
    γ ≤ Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) ∨
      (γ = 2 * Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) ∧
        (C • v = u ∨ C⁻¹ • v = u) ∧ dist w u = dist w v) := by
  let w := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC)
  let θ := 2 * Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)
  have hn := least_elliptic_realSL_order_two_le C hC hleast
  have hnR : (2 : ℝ) ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) := by linarith only [hnR]
  have hθ : 0 < θ := div_pos (mul_pos (by norm_num) Real.pi_pos) hn0
  have hθπ : θ ≤ Real.pi := (div_le_iff₀ hn0).mpr (by nlinarith only [hnR, Real.pi_pos])
  obtain ⟨q, a, b, hu, hq, _hb, hr, hroot⟩ := least_elliptic_exists_normalized_disc_root C hC hleast
  let F : ℍ → 𝔻 := fun x => _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (q • x)
  let R := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL a b hu
  have hF : Function.Injective F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective.comp (isometry_smul ℍ q).injective
  have hw0 : F w = 0 := by
    apply Complex.UnitDisc.coe_injective
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyFormula ((q • w : ℍ) : ℂ) = 0
    rw [hq]
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyFormula, UpperHalfPlane.coe_I, sub_self,
      zero_div]
  have hnonzero (x : ℍ) (hx : w ≠ x) : (F x : ℂ) ≠ 0 := by
    intro he
    have hFx : F x = 0 := Complex.UnitDisc.coe_injective he
    exact hx (hF (hw0.trans hFx.symm))
  have hdist (x y : ℍ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (F x) (F y) = dist x y := by
    simp only [F, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc, dist_smul]
  have hmap (D : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action (q * D * q⁻¹) (F v) = F (D • v) := by
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action, F,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc, mul_smul, inv_smul_smul]
  have hRmap : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action R (F v) = F (C • v) := by dsimp only [R]; rw [← hr]; exact hmap C
  have hRimap : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action R⁻¹ (F v) = F (C⁻¹ • v) := by
    dsimp only [R]
    rw [← hr]
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using hmap C⁻¹
  have hinverse (α : ℝ)
      (ha : ∀ z : 𝔻, (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action R z : ℂ) = Complex.exp ((α : ℂ) *
        Complex.I) * z) :
      ∀ z : 𝔻, (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action R⁻¹ z : ℂ) = Complex.exp ((-α : ℝ) * Complex.I) * z := by
    intro z
    have hcomp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action R (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action R⁻¹ z) = z := by
      simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc, smul_inv_smul,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    have he := ha (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action R⁻¹ z)
    rw [hcomp] at he
    apply mul_left_cancel₀ (Complex.exp_ne_zero ((α : ℂ) * Complex.I))
    have hsum : (α : ℂ) * Complex.I + ((-α : ℝ) : ℂ) * Complex.I = 0 := by push_cast; ring
    simpa only [← mul_assoc, ← Complex.exp_add, hsum, Complex.exp_zero, one_mul] using he.symm
  have hminF : ∀ x ∈ ({(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation (Complex.exp ((θ : ℂ) *
    Complex.I))
        (Complex.norm_exp_ofReal_mul_I θ) (F v)),
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation (Complex.exp ((-θ : ℝ) * Complex.I))
        (Complex.norm_exp_ofReal_mul_I (-θ)) (F v))} : Set 𝔻),
      x ≠ F u → _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (F u) (F v) ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (F u) x := by
    have hbound (D : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hD : D ∈ ({C, C⁻¹} : Set _))
        (x : 𝔻) (hx : x = F (D • v)) (hne : x ≠ F u) :
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (F u) (F v) ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (F u) x := by
      rw [hx, hdist, hdist]
      exact hmin D hD (fun he => hne (hx.trans (congrArg F he)))
    rcases hroot with hplus | hminus
    · have hpi := hinverse θ hplus
      intro x hx hne
      rcases mem_insert_iff.mp hx with hx | hx
      · apply hbound C (by simp) x _ hne
        rw [hx, ← hRmap]
        apply Complex.UnitDisc.coe_injective
        exact (hplus (F v)).symm
      · apply hbound C⁻¹ (by simp) x _ hne
        rw [mem_singleton_iff.mp hx, ← hRimap]
        apply Complex.UnitDisc.coe_injective
        exact (hpi (F v)).symm
    · have hmi := hinverse (-θ) hminus
      intro x hx hne
      rcases mem_insert_iff.mp hx with hx | hx
      · apply hbound C⁻¹ (by simp) x _ hne
        rw [hx, ← hRimap]
        apply Complex.UnitDisc.coe_injective
        simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation_coe, neg_neg] using (hmi (F
          v)).symm
      · apply hbound C (by simp) x _ hne
        rw [mem_singleton_iff.mp hx, ← hRmap]
        apply Complex.UnitDisc.coe_injective
        exact (hminus (F v)).symm
  have hang := centered_disc_angle_eq_hInteriorAngleMeasure q w u v hq hwu hwv
  rcases disc_minimal_rotation_angle_dichotomy (F u) (F v) (hnonzero u hwu)
    (hnonzero v hwv) θ hθ hθπ hminF with hsmall | ⟨hcollision, hnorm⟩
  · left
    rw [← hang]
    convert hsmall using 1
    dsimp only [θ]
    ring
  · right
    refine ⟨?_, ?_, ?_⟩
    · rw [← hang]
      exact hcollision
    · have hgap : θ / 2 < angle (F u : ℂ) (F v : ℂ) := by rw [hcollision]; linarith only [hθ]
      rcases disc_rotation_step_decreases_distance (F u) (F v) (hnonzero u hwu)
        (hnonzero v hwv) θ hθ hθπ hgap with hp | hm
      · have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation (Complex.exp ((θ : ℂ) * Complex.I))
            (Complex.norm_exp_ofReal_mul_I θ) (F v) = F u := by
          by_contra hn
          exact not_lt_of_ge (hminF _ (by simp) hn) hp
        rcases hroot with hplus | hminus
        · left
          apply hF
          rw [← hRmap, ← he]
          apply Complex.UnitDisc.coe_injective
          exact hplus (F v)
        · right
          have hmi := hinverse (-θ) hminus
          apply hF
          rw [← hRimap, ← he]
          apply Complex.UnitDisc.coe_injective
          simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation_coe, neg_neg] using hmi (F v)
      · have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation (Complex.exp ((-θ : ℝ) *
        Complex.I))
            (Complex.norm_exp_ofReal_mul_I (-θ)) (F v) = F u := by
          by_contra hn
          exact not_lt_of_ge (hminF _ (by simp) hn) hm
        rcases hroot with hplus | hminus
        · right
          have hpi := hinverse θ hplus
          apply hF
          rw [← hRimap, ← he]
          apply Complex.UnitDisc.coe_injective
          exact hpi (F v)
        · left
          apply hF
          rw [← hRmap, ← he]
          apply Complex.UnitDisc.coe_injective
          exact hminus (F v)
    · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_norm_eq_tanh_half_distance,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_norm_eq_tanh_half_distance] at hnorm
      have he := Real.tanh_injective hnorm
      rw [← hw0, hdist, hdist] at he
      linarith only [he]

theorem HalfPlaneFuchsianGroup.closest_orbit_least_rotation_cut
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (u v : ℍ) (huv : u ≠ v) :
    ∃ D : Matrix.SpecialLinearGroup (Fin
      2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D ∈ H ∧ D • v ≠ u ∧
      ∀ (C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
        (hC : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C))
        (_hleast : HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          C)), _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C ∈ H →
        ∀ (hwu : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC) ≠ u)
          (hwv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C
            ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC) ≠ D • v),
        let w := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC)
        let γ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w u hwu) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w (D • v) hwv)
        γ ≤ Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) ∨
          (γ = 2 * Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) ∧
            (C • (D • v) = u ∨ C⁻¹ • (D • v) = u) ∧ dist w u = dist w (D • v)) := by
  obtain ⟨D, hDH, hDne, hDmin⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.closest_distinct_native_orbit P u v huv
  refine ⟨D, hDH, hDne, ?_⟩
  intro C hC hleast hCH hwu hwv
  apply least_elliptic_minimal_center_angle C hC hleast u (D • v) hwu hwv
  intro E hE hEne
  have hEH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E ∈ H := by
    rcases mem_insert_iff.mp hE with rfl | hE
    · exact hCH
    · rw [mem_singleton_iff.mp hE, map_inv]
      exact H.inv_mem hCH
  have hEDH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (E * D) ∈ H := by
    rw [map_mul]
    exact H.mul_mem hEH hDH
  have he : (E * D) • v ≠ u := by simpa only [mul_smul] using hEne
  simpa only [mul_smul] using hDmin (E * D) hEDH he



open scoped UpperHalfPlane MatrixGroups OnePoint

theorem HalfPlaneFuchsianGroup.elliptic_exists_native_least_generator
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H ∧ HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) =
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ∧
      Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) =
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H
          (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  let w := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ((w : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p
  have hle : K ≤ H := fun f hf => ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H
    p f).mp hf).1
  let : IsCyclic K := P.asFuchsianDisc.stabilizer_isCyclic p
  have hfinite : Finite K := by
    apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_finite_of_common_H3_fixed K
      (discreteMobius_subgroup_of_le H K P.discrete
        hle) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed w)
    intro f hf
    obtain ⟨B, hB⟩ := mobius_preserves_halfPlane_exists_SL f (P.preserves ⟨f, hle hf⟩)
    have hfix := ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p f).mp hf).2
    change f.val ((w : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((w : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hfix
    rw [← hB, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action] at hfix
    have hwB : B • w = w := UpperHalfPlane.ext (OnePoint.coe_eq_coe.mp hfix)
    rw [← hB, _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_realSL, hwB]
  let : Finite K := hfinite
  have hAf : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val p = p := by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((w : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((w : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ w).mpr rfl]
  have hAK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ K := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p _).mpr ⟨hAH, hAf⟩
  obtain ⟨g, hg, hgen, hleast, _ht, _q, _hmodel⟩ :=
    primitive_finite_cyclic_exists_least_rotation K (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A) hAK hA.1
  have hg0 : g ≠ 1 := by
    intro he
    have hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ Subgroup.zpowers g := hgen ▸ hAK
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [he, one_zpow] at hn
    exact hA.1 hn.symm
  obtain ⟨hgH, hgp⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p g).mp hg
  obtain ⟨B, hB⟩ := mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g, hgH⟩)
  have hBE : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := hB ▸ primitive_elliptic_of_finite_subgroup K g hg hg0
  have hBw := primitive_realSL_elliptic_center_eq B hBE w (hB ▸ hgp)
  refine ⟨B, hBE, hB ▸ hgH, hB ▸ hleast, hBw, ?_⟩
  simpa only [hB] using hgen

theorem realSL_nonidentity_power_trace_bound
    (C A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hC : IsOfFinOrder (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)) (hA0 :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1)
    (hpower : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ Subgroup.zpowers
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)) :
    (Matrix.trace A.val)^2 ≤ 4*(Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)))^2 := by
  let K := Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)
  have hcard : Nat.card K = orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    C) := Nat.card_zpowers _
  let : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hC.orderOf_pos.ne')
  let : IsCyclic K := inferInstance
  have hC0 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C ≠ 1 := by
    intro he
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hpower
    rw [he, one_zpow] at hn
    exact hA0 hn.symm
  have hN : 1 < Nat.card K := by
    rw [hcard]
    have hn1 : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) ≠ 1 :=
      fun he => hC0 (orderOf_eq_one_iff.mp he)
    have hnpos := hC.orderOf_pos
    omega
  obtain ⟨q, hmodel⟩ := primitive_finite_cyclic_full_root_model K
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) hpower hA0
  have ht := primitive_realSL_trace_bound_of_full_root_model K hN q hmodel A hpower hA0
  rwa [hcard] at ht

theorem least_elliptic_nonidentity_power_trace_bound
    (C A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hC : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C))
    (hleast : HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C))
    (hA0 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1)
    (hpower : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ Subgroup.zpowers
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)) :
    (Matrix.trace A.val)^2 ≤ 4*(Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)))^2 := by
  apply realSL_nonidentity_power_trace_bound C A _ hA0 hpower
  apply orderOf_pos_iff.mp
  have ht := hleast.squaredTrace_order
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace] at ht
  have htR : (Matrix.trace C.val)^2 =
      4*(Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        C)))^2 := Complex.ofReal_injective ht
  have hn0 : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) ≠ 0 := by
    intro hn
    rw [hn, Nat.cast_zero, div_zero, Real.cos_zero] at htR
    have he := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC
    nlinarith only [htR, he]
  omega


open scoped UpperHalfPlane MatrixGroups OnePoint

theorem HalfPlaneFuchsianGroup.minimal_reflection_center_primitive_cut
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (w u v : ℍ) (hwu : w ≠ u) (hwv : w ≠ v)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H)
    (he : ∀ x : ℍ, A • x = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w u
      hwu).supportLine.reflection
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w v hwv).supportLine.reflection x))
    (hmin : ∀ D : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D
      ∈ H →
      D • v ≠ u → dist u v ≤ dist u (D • v)) :
    ∃ C : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ hC : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C ∈ H ∧ HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC) = w ∧
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w u hwu)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w v hwv) =
          Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)) ∨
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w u hwu)
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w v hwv) =
          2 * Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) ∧
          (C • v = u ∨ C⁻¹ • v = u) ∧ dist w u = dist w v)) := by
  let R := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w u hwu
  let S := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w v hwv
  let γ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S
  have hAw : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) = w := by
    have hfix : A • w = w := by
      rw [he, (S.supportLine.reflection_fixed_iff w).mpr S.start_mem_support,
        (R.supportLine.reflection_fixed_iff w).mpr R.start_mem_support]
    exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ w).mp hfix).symm
  obtain ⟨C, hC, hCH, hleast, hCA, hgen⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_exists_native_least_generator P A hA hAH
  have hCw : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC) = w := hCA.trans hAw
  have hwuC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC) ≠ u := by rwa [hCw]
  have hwvC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC) ≠ v := by rwa [hCw]
  have hCM : ∀ D ∈ ({C, C⁻¹} : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)),
      D • v ≠ u → dist u v ≤ dist u (D • v) := by
    intro D hD
    apply hmin D
    rcases mem_insert_iff.mp hD with rfl | hD
    · exact hCH
    · rw [mem_singleton_iff.mp hD, map_inv]
      exact H.inv_mem hCH
  have hcut : γ ≤ Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) ∨
      (γ = 2 * Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) ∧
        (C • v = u ∨ C⁻¹ • v = u) ∧ dist w u = dist w v) := by
    have hγC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC)) u hwuC)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC)) v hwvC) = γ := by
      clear hAw
      subst w
      rfl
    have hh := least_elliptic_minimal_center_angle C hC hleast u v hwuC hwvC hCM
    dsimp only at hh
    rwa [hγC, hCw] at hh
  refine ⟨C, hC, hCH, hleast, hCw, ?_⟩
  rcases hcut with hsmall | hcollision
  · left
    have hApow : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) := by
      rw [hgen]
      apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H _ _).mpr
      refine ⟨hAH, ?_⟩
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ _).mpr rfl]
    have htrace := least_elliptic_nonidentity_power_trace_bound C A hC hleast hA.1 hApow
    have hγtrace := native_ray_reflection_product_trace_square A R S he
    have hn := least_elliptic_realSL_order_two_le C hC hleast
    have hnR : (2 : ℝ) ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) := by linarith only [hnR]
    have hδ0 : 0 ≤ Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) := (div_pos
      Real.pi_pos hn0).le
    have hδπ : Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) ≤ Real.pi / 2 :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hnR
    have hγ0 : 0 ≤ γ := InnerProductGeometry.angle_nonneg _ _
    have hcγ : 0 ≤ Real.cos γ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith only [hγ0, Real.pi_pos], hsmall.trans hδπ⟩
    have hcδ : 0 ≤ Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith only [hδ0, Real.pi_pos], hδπ⟩
    have hcos : Real.cos γ ≤ Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)) := by
      apply (sq_le_sq₀ hcγ hcδ).mp
      nlinarith only [htrace, hγtrace]
    apply le_antisymm hsmall
    by_contra hnot
    have hc := Real.strictAntiOn_cos ⟨hγ0, by linarith only [hsmall, hδπ, Real.pi_pos]⟩
      ⟨hδ0, by linarith only [hδπ, Real.pi_pos]⟩ (lt_of_not_ge hnot)
    exact not_lt_of_ge hcos hc
  · exact Or.inr hcollision

end LowDimensionalTopology.Geometry.Fuchsian
