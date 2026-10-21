/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPositiveReplacements
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
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem triangle_cosines_nonneg_of_product_nonneg {κ η : ℝ}
    (hκ : κ ∈ Ioo 0 Real.pi) (hη : η ∈ Ioo 0 Real.pi)
    (hs : κ+η < Real.pi) (hp : 0 ≤ Real.cos κ*Real.cos η) :
    0 ≤ Real.cos κ ∧ 0 ≤ Real.cos η := by
  have hfirst {a b : ℝ} (ha : a ∈ Ioo 0 Real.pi) (hb : b ∈ Ioo 0 Real.pi)
      (hsum : a+b < Real.pi) (hprod : 0 ≤ Real.cos a*Real.cos b) : 0 ≤ Real.cos a := by
    by_contra hn
    have haneg : Real.cos a < 0 := lt_of_not_ge hn
    have hbnonpos : Real.cos b ≤ 0 := by nlinarith only [hprod, haneg]
    have halt : Real.pi/2 < a := by
      by_contra h
      have ha' : a ≤ Real.pi/2 := le_of_not_gt h
      have hnn := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith only [ha.1, Real.pi_pos]) ha'
      exact not_lt_of_ge hnn haneg
    have hble : Real.pi/2 ≤ b := by
      by_contra h
      have hb' : b < Real.pi/2 := lt_of_not_ge h
      have hpos := Real.cos_pos_of_mem_Ioo ⟨by linarith only [hb.1, Real.pi_pos], hb'⟩
      exact not_lt_of_ge hbnonpos hpos
    linarith only [halt, hble, hsum]
  exact ⟨hfirst hκ hη hs hp, hfirst hη hκ (by linarith only [hs])
    (by simpa only [mul_comm] using hp)⟩

theorem elliptic_triangle_positive_angle_identification {κ η ψ δ ε D : ℝ}
    (hκ : κ ∈ Ioo 0 Real.pi) (hη : η ∈ Ioo 0 Real.pi)
    (hψ : ψ ∈ Ioo 0 Real.pi) (hs : κ+η+ψ < Real.pi)
    (hδ : δ ∈ Ioc 0 (Real.pi/2)) (hε : ε ∈ Ioc 0 (Real.pi/2))
    (hD : 0 < D)
    (hκδ : (Real.cos κ)^2 = (Real.cos δ)^2)
    (hηε : (Real.cos η)^2 = (Real.cos ε)^2)
    (hcos : Real.cos ψ = D*Real.sin δ*Real.sin ε-Real.cos κ*Real.cos η)
    (htrace : (Real.cos ψ)^2 =
      (D*Real.sin δ*Real.sin ε-Real.cos δ*Real.cos ε)^2) :
    κ=δ ∧ η=ε := by
  let T := D*Real.sin δ*Real.sin ε
  let x := Real.cos δ*Real.cos ε
  let y := Real.cos κ*Real.cos η
  have hsδ := Real.sin_pos_of_pos_of_lt_pi hδ.1
    (by linarith only [hδ.2, Real.pi_pos])
  have hsε := Real.sin_pos_of_pos_of_lt_pi hε.1
    (by linarith only [hε.2, Real.pi_pos])
  have hT : 0 < T := mul_pos (mul_pos hD hsδ) hsε
  have hprod : y^2=x^2 := by
    dsimp only [y, x]
    rw [mul_pow, mul_pow, hκδ, hηε]
  have heq : (T-y)^2=(T-x)^2 := by
    change (D*Real.sin δ*Real.sin ε-Real.cos κ*Real.cos η)^2 = _
    rw [←hcos]
    exact htrace
  have hdif : 2*T*(y-x)=0 := by nlinarith only [hprod, heq]
  have hyx : y=x := sub_eq_zero.mp
    ((mul_eq_zero.mp hdif).resolve_left (mul_ne_zero (by norm_num) hT.ne'))
  have hcδ : 0 ≤ Real.cos δ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith only [hδ.1, Real.pi_pos]) hδ.2
  have hcε : 0 ≤ Real.cos ε := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith only [hε.1, Real.pi_pos]) hε.2
  have hy0 : 0 ≤ Real.cos κ*Real.cos η := by
    change 0 ≤ y
    rw [hyx]
    exact mul_nonneg hcδ hcε
  have hcs := triangle_cosines_nonneg_of_product_nonneg hκ hη
    (by linarith only [hs, hψ.1]) hy0
  have hceκ : Real.cos κ = Real.cos δ := by nlinarith only [hκδ, hcs.1, hcδ]
  have hceη : Real.cos η = Real.cos ε := by nlinarith only [hηε, hcs.2, hcε]
  exact ⟨Real.strictAntiOn_cos.injOn ⟨hκ.1.le, hκ.2.le⟩
      ⟨hδ.1.le, by linarith only [hδ.2, Real.pi_pos]⟩ hceκ,
    Real.strictAntiOn_cos.injOn ⟨hη.1.le, hη.2.le⟩
      ⟨hε.1.le, by linarith only [hε.2, Real.pi_pos]⟩ hceη⟩

open scoped UpperHalfPlane MatrixGroups OnePoint

theorem elliptic_pair_actual_triangle_positive_angles
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A))
    (hB : Mobius.MobiusElliptic (realSLMobius B))
    (huv : hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB))
    (hAB : Mobius.MobiusElliptic (realSLMobius (A * B)))
    (δ ε : ℝ) (hδ : δ ∈ Ioc 0 (Real.pi / 2)) (hε : ε ∈ Ioc 0 (Real.pi / 2))
    (hangleA : hEllipticRotationAngle A hA = 2 * δ)
    (hangleB : hEllipticRotationAngle B hB = 2 * ε) :
    ∃ T : HTriangle,
      T.a = hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB) ∧
      T.c = hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA) ∧
      T.b = hEllipticCenter (A * B) ((realSLMobius_elliptic_iff (A * B) hAB.1).mp hAB) ∧
      T.gamma = δ ∧ T.alpha = ε ∧
      (Matrix.trace (A * B).val)^2 = 4 * (Real.cos T.beta)^2 ∧
      Subgroup.closure ({hSLIsometry A, hSLIsometry B} : Set (ℍ ≃ᵢ ℍ)) =
        Fuchsian.triangleConformalGroup T.toClosedHTriangle := by
  obtain ⟨T, ha, hc, hb, htrA, htrB, htrAB, hG⟩ :=
    Fuchsian.elliptic_pair_actual_triangle_center_angles A B hA hB huv hAB
  have hκδ : (Real.cos T.gamma)^2 = (Real.cos δ)^2 := by
    have hh := (hEllipticRotationAngle_spec A hA).2.2.2
    rw [hangleA, show 2 * δ / 2 = δ by ring] at hh
    nlinarith only [htrA, hh]
  have hηε : (Real.cos T.alpha)^2 = (Real.cos ε)^2 := by
    have hh := (hEllipticRotationAngle_spec B hB).2.2.2
    rw [hangleB, show 2 * ε / 2 = ε by ring] at hh
    nlinarith only [htrB, hh]
  have hsδ : Real.sin T.gamma = Real.sin δ := by
    have hpos := Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.2.2.1 T.angles_mem_Ioo.2.2.2
    have hposδ := Real.sin_pos_of_pos_of_lt_pi hδ.1 (by linarith only [hδ.2, Real.pi_pos])
    nlinarith only [Real.sin_sq_add_cos_sq T.gamma, Real.sin_sq_add_cos_sq δ, hκδ, hpos, hposδ]
  have hsε : Real.sin T.alpha = Real.sin ε := by
    have hpos := Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.1.1 T.angles_mem_Ioo.1.2
    have hposε := Real.sin_pos_of_pos_of_lt_pi hε.1 (by linarith only [hε.2, Real.pi_pos])
    nlinarith only [Real.sin_sq_add_cos_sq T.alpha, Real.sin_sq_add_cos_sq ε, hηε, hpos, hposε]
  have hden : Real.sin T.gamma * Real.sin T.alpha ≠ 0 :=
    mul_ne_zero (Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.2.2.1 T.angles_mem_Ioo.2.2.2).ne'
      (Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.1.1 T.angles_mem_Ioo.1.2).ne'
  have hcos : Real.cos T.beta = Real.cosh T.lengthB * Real.sin δ * Real.sin ε -
      Real.cos T.gamma * Real.cos T.alpha := by
    have hh := (eq_div_iff hden).mp T.cosine_rule_II_B
    rw [hsδ, hsε] at hh
    nlinarith only [hh]
  have htrace : (Real.cos T.beta)^2 =
      (Real.cosh T.lengthB * Real.sin δ * Real.sin ε - Real.cos δ * Real.cos ε)^2 := by
    have hh := hElliptic_product_abs_trace A B hA hB
    dsimp only at hh
    rw [← hc, ← ha, hangleA, hangleB, show 2 * δ / 2 = δ by ring,
      show 2 * ε / 2 = ε by ring] at hh
    change |Matrix.trace (A * B).val| / 2 =
      |Real.cosh T.lengthB * Real.sin δ * Real.sin ε - Real.cos δ * Real.cos ε| at hh
    have hsq := congrArg (fun x : ℝ => x^2) hh
    simp only [div_pow, sq_abs] at hsq
    nlinarith only [hsq, htrAB]
  have hangle := elliptic_triangle_positive_angle_identification T.angles_mem_Ioo.2.2
    T.angles_mem_Ioo.1 T.angles_mem_Ioo.2.1
    (by linarith only [T.angle_sum_lt_pi]) hδ hε (Real.cosh_pos _)
    hκδ hηε hcos htrace
  exact ⟨T, ha, hc, hb, hangle.1, hangle.2, htrAB, hG⟩

theorem native_triangle_equal_radii_base_angles (T : HTriangle)
    (hrad : dist T.c T.a = dist T.c T.b) : T.alpha = T.beta := by
  have hlen : T.lengthA = T.lengthB := by
    simpa only [HTriangle.lengthA, HTriangle.lengthB, dist_comm] using hrad.symm
  have hA := T.cosine_rule_A
  have hB := T.cosine_rule_B
  rw [← hlen] at hA hB
  have hfac : Real.sinh T.lengthA * Real.sinh T.lengthC ≠ 0 :=
    mul_ne_zero (Real.sinh_pos_iff.mpr T.lengths_pos.1).ne'
      (Real.sinh_pos_iff.mpr T.lengths_pos.2.2).ne'
  have hcos : Real.cos T.alpha = Real.cos T.beta := by
    apply mul_left_cancel₀ hfac
    nlinarith only [hA, hB]
  exact Real.injOn_cos ⟨T.angles_mem_Ioo.1.1.le, T.angles_mem_Ioo.1.2.le⟩
    ⟨T.angles_mem_Ioo.2.1.1.le, T.angles_mem_Ioo.2.1.2.le⟩ hcos

theorem native_isosceles_half_angle_cosine (T : HTriangle)
    (hrad : dist T.c T.a = dist T.c T.b) :
    Real.cosh (dist T.c T.b) * Real.sin T.beta * Real.sin (T.gamma / 2) =
      Real.cos T.beta * Real.cos (T.gamma / 2) := by
  have hbase := native_triangle_equal_radii_base_angles T hrad
  have hsβ := Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.2.1.1 T.angles_mem_Ioo.2.1.2
  have hsγ := Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.2.2.1 T.angles_mem_Ioo.2.2.2
  have hcγ : 0 < Real.cos (T.gamma / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [T.angles_mem_Ioo.2.2.1, Real.pi_pos],
      by linarith [T.angles_mem_Ioo.2.2.2]⟩
  have he := (eq_div_iff (mul_pos hsβ hsγ).ne').mp T.cosine_rule_II_A
  rw [hbase] at he
  have hsin : Real.sin T.gamma = 2 * Real.sin (T.gamma / 2) * Real.cos (T.gamma / 2) := by
    simpa only [show 2 * (T.gamma / 2) = T.gamma by ring] using Real.sin_two_mul (T.gamma / 2)
  have hcos : Real.cos T.gamma = 2 * Real.cos (T.gamma / 2)^2 - 1 := by
    simpa only [show 2 * (T.gamma / 2) = T.gamma by ring] using Real.cos_two_mul (T.gamma / 2)
  rw [hsin, hcos] at he
  have he' : (2 * Real.cos (T.gamma / 2)) *
      (Real.cosh T.lengthA * Real.sin T.beta * Real.sin (T.gamma / 2)) =
      (2 * Real.cos (T.gamma / 2)) * (Real.cos T.beta * Real.cos (T.gamma / 2)) := by
    nlinarith only [he]
  have hh := mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hcγ.ne') he'
  simpa only [HTriangle.lengthA, dist_comm] using hh

theorem native_isosceles_fold_product_trace_zero (T : HTriangle)
    (hrad : dist T.c T.a = dist T.c T.b)
    (B C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : Mobius.MobiusElliptic (realSLMobius B))
    (hC : Mobius.MobiusElliptic (realSLMobius C))
    (hcenterB : hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB) = T.b)
    (hcenterC : hEllipticCenter C ((realSLMobius_elliptic_iff C hC.1).mp hC) = T.c)
    (hangleB : hEllipticRotationAngle B hB = 2 * T.beta)
    (hangleC : hEllipticRotationAngle C hC = T.gamma) :
    Matrix.trace (B * C).val = 0 := by
  have ht := hElliptic_product_abs_trace B C hB hC
  dsimp only at ht
  rw [hcenterB, hcenterC, hangleB, hangleC, show 2 * T.beta / 2 = T.beta by ring,
    dist_comm T.b T.c] at ht
  have hcos := native_isosceles_half_angle_cosine T hrad
  have he : Real.cosh (dist T.c T.b) * Real.sin T.beta * Real.sin (T.gamma / 2) -
      Real.cos T.beta * Real.cos (T.gamma / 2) = 0 := sub_eq_zero.mpr hcos
  rw [he, abs_zero] at ht
  exact abs_eq_zero.mp (by linarith only [ht])

end LowDimensionalTopology.Geometry.Hyperbolic
