/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPrimitiveRotationGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPositiveReplacements
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticTriangleGeometry
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

theorem native_elliptic_realSL_conjugate (A D : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D * A * D⁻¹)) := by
  have hc : IsConj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D * A * D⁻¹)) :=
    isConj_iff.mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D, by simp only [map_mul, map_inv]⟩
  exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_isConj hc).mp hA

theorem native_elliptic_realSL_conjugate_center (A D : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hAD : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D * A * D⁻¹))) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter (D * A *
      D⁻¹) ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ hAD.1).mp hAD) =
      D • _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) := by
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  have hu : A • u = u := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ u).mpr rfl
  have hfix : (D * A * D⁻¹) • (D • u) = D • u := by
    simp only [mul_smul, inv_smul_smul, hu]
  exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff (D * A * D⁻¹) _ (D • u)).mp
    hfix).symm

theorem elliptic_sin_half_lower_of_trace_bound
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    {δ : ℝ} (hδ : δ ∈ Ioc 0 (Real.pi/2))
    (ht : (Matrix.trace A.val)^2 ≤ 4*(Real.cos δ)^2) :
    Real.sin δ ≤ Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA/2) := by
  have hθ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo A hA
  have hsθ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsδ := Real.sin_pos_of_pos_of_lt_pi hδ.1
    (by linarith only [hδ.2, Real.pi_pos])
  have htrace := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A hA).2.2.2
  nlinarith only [ht, htrace, hsθ, hsδ,
    Real.sin_sq_add_cos_sq δ, Real.sin_sq_add_cos_sq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA/2)]

theorem elliptic_cut_half_angle_cosine_bound {θ δ : ℝ}
    (hθ : θ ∈ Ioo 0 Real.pi) (hδ : δ ∈ Ioc 0 (Real.pi/2))
    (hs : Real.sin δ ≤ Real.sin θ) : |Real.cos θ| ≤ Real.cos δ := by
  have hsθ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsδ := Real.sin_pos_of_pos_of_lt_pi hδ.1
    (by linarith only [hδ.2, Real.pi_pos])
  have hcδ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith only [hδ.1, Real.pi_pos]) hδ.2
  nlinarith only [hs, hsθ, hsδ, hcδ, abs_nonneg (Real.cos θ), sq_abs (Real.cos θ),
    Real.sin_sq_add_cos_sq δ, Real.sin_sq_add_cos_sq θ]

theorem elliptic_cut_product_expression_mono {θ φ δ ε D E : ℝ}
    (hθ : θ ∈ Ioo 0 Real.pi) (hφ : φ ∈ Ioo 0 Real.pi)
    (hδ : δ ∈ Ioc 0 (Real.pi/2)) (hε : ε ∈ Ioc 0 (Real.pi/2))
    (hsδ : Real.sin δ ≤ Real.sin θ) (hsε : Real.sin ε ≤ Real.sin φ)
    (hD : 0 ≤ D) (hED : E ≤ D) :
    E*Real.sin δ*Real.sin ε-Real.cos δ*Real.cos ε ≤
      D*Real.sin θ*Real.sin φ-Real.cos θ*Real.cos φ := by
  have hsd := Real.sin_pos_of_pos_of_lt_pi hδ.1
    (by linarith only [hδ.2, Real.pi_pos])
  have hse := Real.sin_pos_of_pos_of_lt_pi hε.1
    (by linarith only [hε.2, Real.pi_pos])
  have hst := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hcδ := elliptic_cut_half_angle_cosine_bound hθ hδ hsδ
  have hcε := elliptic_cut_half_angle_cosine_bound hφ hε hsε
  have hcd : 0 ≤ Real.cos δ := (abs_nonneg _).trans hcδ
  have hcp : Real.cos θ*Real.cos φ ≤ Real.cos δ*Real.cos ε := by
    apply (le_abs_self _).trans
    rw [abs_mul]
    exact mul_le_mul hcδ hcε (abs_nonneg _) hcd
  have hss : Real.sin δ*Real.sin ε ≤ Real.sin θ*Real.sin φ :=
    mul_le_mul hsδ hsε hse.le hst.le
  have hscaled := mul_le_mul_of_nonneg_left hss hD
  have hdist := mul_nonneg (sub_nonneg.mpr hED) (mul_nonneg hsd.le hse.le)
  nlinarith only [hcp, hscaled, hdist]

theorem elliptic_primitive_cut_expression_le
    (A B G K : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hG : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius G)) (hK :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius K))
    {δ ε : ℝ} (hδ : δ ∈ Ioc 0 (Real.pi/2)) (hε : ε ∈ Ioc 0 (Real.pi/2))
    (hGangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle G hG = 2*δ)
    (hKangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle K hK = 2*ε)
    (hsδ : Real.sin δ ≤ Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA/2))
    (hsε : Real.sin ε ≤ Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2))
    (hd : dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter G
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff G hG.1).mp hG))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter K
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff K hK.1).mp hK)) ≤
      dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))) :
    Real.cosh (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter G
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff G hG.1).mp hG))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter K
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff K hK.1).mp hK)))*
        Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle G
          hG/2)*Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle K hK/2)-
        Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle G
          hG/2)*Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle K hK/2) ≤
      Real.cosh (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)))*
        Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A
          hA/2)*Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2)-
        Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA/2)*Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2) := by
  have hGhalf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle G hG/2=δ := by linarith only [hGangle]
  have hKhalf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle K hK/2=ε := by linarith only [hKangle]
  rw [hGhalf, hKhalf]
  apply elliptic_cut_product_expression_mono (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo A hA)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo B hB) hδ hε hsδ hsε (Real.cosh_pos
      _).le
  apply Real.cosh_le_cosh.mpr
  simpa only [abs_of_nonneg dist_nonneg] using hd

theorem elliptic_primitive_cut_product_elliptic
    (A B G K : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hG : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius G)) (hK :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius K))
    {δ ε : ℝ} (hδ : δ ∈ Ioc 0 (Real.pi/2)) (hε : ε ∈ Ioc 0 (Real.pi/2))
    (hGangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle G hG = 2*δ)
    (hKangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle K hK = 2*ε)
    (hsδ : Real.sin δ ≤ Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA/2))
    (hsε : Real.sin ε ≤ Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2))
    (hd : dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter G
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff G hG.1).mp hG))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter K
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff K hK.1).mp hK)) ≤
      dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)))
    (hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter G
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff G hG.1).mp hG) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter K ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff K hK.1).mp hK))
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B))) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (G*K)) := by
  let O := Real.cosh (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)))*
      Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A
        hA/2)*Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2)-
      Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A
        hA/2)*Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2)
  let N := Real.cosh (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter G
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff G hG.1).mp hG))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter K
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff K hK.1).mp hK)))*
      Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle G
        hG/2)*Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle K hK/2)-
      Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle G
        hG/2)*Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle K hK/2)
  have hcomp := elliptic_primitive_cut_expression_le A B G K hA hB hG hK
    hδ hε hGangle hKangle hsδ hsε hd
  change N ≤ O at hcomp
  have ho := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_abs_trace A B hA hB
  have hn := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_abs_trace G K hG hK
  have hlow := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_expression_gt_neg_one G K hG hK hne
  change |Matrix.trace (A*B).val|/2=|O| at ho
  change |Matrix.trace (G*K).val|/2=|N| at hn
  change -1<N at hlow
  have ht := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff (A*B) hAB.1).mp hAB
  have hto : |Matrix.trace (A*B).val| < 2 := by
    nlinarith only [ht, sq_abs (Matrix.trace (A*B).val), abs_nonneg (Matrix.trace (A*B).val)]
  have ho1 : O<1 := by nlinarith only [ho, hto, le_abs_self O]
  have hn1 : N<1 := hcomp.trans_lt ho1
  have habs : |N|<1 := abs_lt.mpr ⟨hlow, hn1⟩
  have htn : |Matrix.trace (G*K).val|<2 := by linarith only [hn, habs]
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff (G*K)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_ne_one_of_centers_ne G K hG hK hne)).mpr
  nlinarith only [htn, sq_abs (Matrix.trace (G*K).val), abs_nonneg (Matrix.trace (G*K).val)]

theorem elliptic_primitive_cut_product_trace_le_four
    (A B G K : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hG : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius G)) (hK :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius K))
    {δ ε : ℝ} (hδ : δ ∈ Ioc 0 (Real.pi/2)) (hε : ε ∈ Ioc 0 (Real.pi/2))
    (hGangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle G hG = 2*δ)
    (hKangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle K hK = 2*ε)
    (hsδ : Real.sin δ ≤ Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA/2))
    (hsε : Real.sin ε ≤ Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2))
    (hd : dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter G
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff G hG.1).mp hG))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter K
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff K hK.1).mp hK)) ≤
      dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)))
    (hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter G
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff G hG.1).mp hG) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter K ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff K hK.1).mp hK))
    (hAB : (Matrix.trace (A*B).val)^2 ≤ 4) :
    (Matrix.trace (G*K).val)^2 ≤ 4 := by
  let O := Real.cosh (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)))*
      Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A
        hA/2)*Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2)-
      Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A
        hA/2)*Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2)
  let N := Real.cosh (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter G
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff G hG.1).mp hG))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter K
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff K hK.1).mp hK)))*
      Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle G
        hG/2)*Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle K hK/2)-
      Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle G
        hG/2)*Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle K hK/2)
  have hcomp := elliptic_primitive_cut_expression_le A B G K hA hB hG hK
    hδ hε hGangle hKangle hsδ hsε hd
  change N ≤ O at hcomp
  have ho := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_abs_trace A B hA hB
  have hn := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_abs_trace G K hG hK
  have hlow := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_expression_gt_neg_one G K hG hK hne
  change |Matrix.trace (A*B).val|/2=|O| at ho
  change |Matrix.trace (G*K).val|/2=|N| at hn
  change -1<N at hlow
  have hto : |Matrix.trace (A*B).val| ≤ 2 := by
    nlinarith only [hAB, sq_abs (Matrix.trace (A*B).val), abs_nonneg (Matrix.trace (A*B).val)]
  have ho1 : O≤1 := by nlinarith only [ho, hto, le_abs_self O]
  have hn1 : N≤1 := hcomp.trans ho1
  have habs : |N|≤1 := abs_le.mpr ⟨hlow.le, hn1⟩
  have htn : |Matrix.trace (G*K).val|≤2 := by linarith only [hn, habs]
  nlinarith only [htn, sq_abs (Matrix.trace (G*K).val), abs_nonneg (Matrix.trace (G*K).val)]

theorem HalfPlaneFuchsianGroup.exists_minimal_positive_elliptic_pair
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) (hBH :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H)
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B)))
    (huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)) :
    ∃ C E : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∃ hC : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C), ∃ hE : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C ∈ H ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E ∈ H ∧
      HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        C) ∧ HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle C hC = 2 * Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle E hE = 2 * Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E) ∧
      Real.sin (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        C)) ≤ Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2) ∧
      Real.sin (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        E)) ≤ Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB / 2) ∧
      let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC)
      let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter E ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff E hE.1).mp hE)
      dist u v ≤ dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)) ∧
      u ≠ v ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (C * E)) ∧
      (∀ F : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F ∈ H →
        F • v ≠ u → dist u v ≤ dist u (F • v)) := by
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
  obtain ⟨D, hDH, hDne, hDmin⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.closest_distinct_native_orbit P u v huv
  let B' := D * B * D⁻¹
  have hB' : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B') := native_elliptic_realSL_conjugate B D hB
  have hB'H : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B' ∈ H := by
    simp only [B', map_mul, map_inv]
    exact H.mul_mem (H.mul_mem hDH hBH) (H.inv_mem hDH)
  have hB'center : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B' ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B' hB'.1).mp hB') = D • v :=
    native_elliptic_realSL_conjugate_center B D hB hB'
  obtain ⟨C, hC, hCH, hleastC, hangleC, hcenterC, _hstabC, hpowC, _horderC⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_exists_native_positive_replacement P A hA hAH
  obtain ⟨E, hE, hEH, hleastE, hangleE, hcenterE, _hstabE, hpowE, _horderE⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_exists_native_positive_replacement P B' hB' hB'H
  let δ := Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)
  let ε := Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E)
  have hsmall (F : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (hF : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F)) (hFl : HasLeastEllipticRotation
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F)) :
      Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F) ∈ Ioc 0 (Real.pi / 2) := by
    have hn := least_elliptic_realSL_order_two_le F hF hFl
    have hnR : (2 : ℝ) ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F) := by linarith only [hnR]
    exact ⟨div_pos Real.pi_pos hn0, div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hnR⟩
  have hδ : δ ∈ Ioc 0 (Real.pi / 2) := hsmall C hC hleastC
  have hε : ε ∈ Ioc 0 (Real.pi / 2) := hsmall E hE hleastE
  have hsinC := elliptic_sin_half_lower_of_trace_bound A hA hδ
    (least_elliptic_nonidentity_power_trace_bound C A hC hleastC hA.1 hpowC)
  have htrE := least_elliptic_nonidentity_power_trace_bound E B' hE hleastE hB'.1 hpowE
  have htrB : (Matrix.trace B.val)^2 ≤ 4 * (Real.cos ε)^2 := by
    rw [show Matrix.trace B'.val = Matrix.trace B.val from
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation B D] at htrE
    exact htrE
  have hsinE := elliptic_sin_half_lower_of_trace_bound B hB hε htrB
  have hcentE : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter E ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff E hE.1).mp hE) = D • v :=
    hcenterE.trans hB'center
  have hd : dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter E ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff E hE.1).mp hE)) ≤ dist u v := by
    rw [hcenterC, hcentE]
    have hh := hDmin 1 (by rw [map_one]; exact H.one_mem) (by simpa only [one_smul] using huv.symm)
    simpa only [one_smul] using hh
  have hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter E ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff E hE.1).mp hE) := by
    rw [hcenterC, hcentE]
    exact hDne.symm
  have hproduct : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (C * E)) :=
    elliptic_primitive_cut_product_elliptic A B C E hA hB hC hE hδ hε
      (by convert hangleC using 1; dsimp only [δ]; ring)
      (by convert hangleE using 1; dsimp only [ε]; ring) hsinC hsinE hd hne hAB
  refine ⟨C, E, hC, hE, hCH, hEH, hleastC, hleastE, hangleC, hangleE,
    hsinC, hsinE, hd, hne, hproduct, ?_⟩
  intro F hFH hFne
  rw [hcenterC, hcentE] at hFne ⊢
  have hFDH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (F * D) ∈ H := by rw [map_mul]; exact H.mul_mem hFH hDH
  have hh := hDmin (F * D) hFDH (by simpa only [mul_smul] using hFne)
  simpa only [mul_smul] using hh

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
theorem native_pair_mobius_range_eq_closure
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (K : Subgroup (ℍ ≃ᵢ ℍ))
    (hK : K ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (hgen : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B} : Set (ℍ ≃ᵢ ℍ)) = K) :
    (nativeConformalSubgroupMobiusHom K hK).range =
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) := by
  let F := nativeConformalSubgroupMobiusHom K hK
  let J := Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hm : ∀ f (hf : f ∈ Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B} : Set (ℍ ≃ᵢ ℍ))), F ⟨f, hgen ▸ hf⟩ ∈ J := by
    intro f hf
    induction hf using Subgroup.closure_induction with
    | mem f hf =>
      rcases hf with rfl | rfl
      · rw [nativeConformalSubgroupMobiusHom_matrix]
        exact Subgroup.subset_closure (by simp)
      · rw [nativeConformalSubgroupMobiusHom_matrix]
        exact Subgroup.subset_closure (by simp)
    | one =>
      change F 1 ∈ J
      rw [map_one]
      exact J.one_mem
    | mul x y hx hy ihx ihy =>
      have he : (⟨x*y, _⟩ : K) = (⟨x, hgen ▸ hx⟩ : K)*⟨y, hgen ▸ hy⟩ := rfl
      rw [he, map_mul]
      exact J.mul_mem ihx ihy
    | inv x hx ih =>
      have he : (⟨x⁻¹, _⟩ : K) = (⟨x, hgen ▸ hx⟩ : K)⁻¹ := rfl
      rw [he, map_inv]
      exact J.inv_mem ih
  apply le_antisymm
  · rintro f ⟨g, rfl⟩
    exact hm g.val (hgen.symm ▸ g.property)
  · apply (Subgroup.closure_le _).mpr
    rintro f (rfl | rfl)
    · have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A ∈ K := hgen ▸ Subgroup.subset_closure (by simp)
      exact ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A, hA⟩,
        nativeConformalSubgroupMobiusHom_matrix K hK A hA⟩
    · have hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B ∈ K := hgen ▸ Subgroup.subset_closure (by simp)
      exact ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B, hB⟩,
        nativeConformalSubgroupMobiusHom_matrix K hK B hB⟩

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
theorem native_pair_isMobiusTriangleGroup
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (K : Subgroup (ℍ ≃ᵢ ℍ))
    (hK : K ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (hgen : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B} : Set (ℍ ≃ᵢ ℍ)) = K)
    (htri : IsTriangleGroup K) :
    IsMobiusTriangleGroup
      (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  rw [←native_pair_mobius_range_eq_closure A B K hK hgen]
  exact isMobiusTriangleGroup_native_image K hK htri

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
theorem elliptic_half_turn_product_isMobiusTriangleGroup
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))
    (p q : ℕ) (hp : 2≤p) (hq : 2≤q)
    (hangleA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA=2*Real.pi/(p:ℝ))
    (hangleB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB=2*Real.pi/(q:ℝ))
    (htrace : Matrix.trace (A*B).val=0) :
    IsMobiusTriangleGroup
      (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hqR : (2:ℝ)≤q := by exact_mod_cast hq
  have hp0 : (0:ℝ)<p := by linarith only [hpR]
  have hq0 : (0:ℝ)<q := by linarith only [hqR]
  have hδ : Real.pi/(p:ℝ)∈Ioc 0 (Real.pi/2) :=
    ⟨div_pos Real.pi_pos hp0,
      div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hpR⟩
  have hε : Real.pi/(q:ℝ)∈Ioc 0 (Real.pi/2) :=
    ⟨div_pos Real.pi_pos hq0,
      div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hqR⟩
  have hAB0 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_ne_one_of_centers_ne A B hA hB huv
  have hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B)) :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff (A*B) hAB0).mpr (by rw [htrace]; norm_num)
  obtain ⟨T, _ha, _hc, _hb, hγ, hα, htr, hgen⟩ :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_pair_actual_triangle_positive_angles A B hA hB huv hAB
      (Real.pi/(p:ℝ)) (Real.pi/(q:ℝ)) hδ hε
      (by simpa only [mul_div_assoc] using hangleA)
      (by simpa only [mul_div_assoc] using hangleB)
  have hβcos : Real.cos T.beta=0 := by
    rw [htrace] at htr
    nlinarith only [htr]
  have hβ : T.beta=Real.pi/2 := Real.strictAntiOn_cos.injOn
    ⟨T.angles_mem_Ioo.2.1.1.le, T.angles_mem_Ioo.2.1.2.le⟩
    ⟨by positivity, by linarith only [Real.pi_pos]⟩
    (by rw [Real.cos_pi_div_two]; exact hβcos)
  have ht : IsTriangleGroup (triangleConformalGroup T.toClosedHTriangle) := by
    refine ⟨(q:ℕ∞), (2:ℕ∞), (p:ℕ∞), ?_, ?_, ?_, T.toClosedHTriangle, ?_, ?_, ?_, rfl⟩
    · exact_mod_cast hq
    · norm_num
    · exact_mod_cast hp
    · rw [T.closed_angles.1, hα, triangleOrderAngle_nat]
    · rw [T.closed_angles.2.1, hβ]
      norm_num [triangleOrderAngle]
    · rw [T.closed_angles.2.2, hγ, triangleOrderAngle_nat]
  exact native_pair_isMobiusTriangleGroup A B _ inf_le_right hgen ht

theorem HalfPlaneFuchsianGroup.minimal_center_primitive_cut_of_trace
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (w u v : ℍ) (hwu : w ≠ u) (hwv : w ≠ v)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H)
    (hAw : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) = w)
    (hangle_trace : (Matrix.trace A.val)^2 = 4 *
      (Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w u hwu)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough w v hwv)))^2)
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
    have hγtrace := hangle_trace
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

/-- The genuine minimal positive pair contains a genuine reciprocal-angle triangle
subgroup, including the source's right-triangle fold alternative. -/
theorem HalfPlaneFuchsianGroup.minimal_positive_elliptic_pair_contains_triangle
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) (hBH :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H)
    (hlA : HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hlB : HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (haA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA = 2 * Real.pi / orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (haB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB = 2 * Real.pi / orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B)))
    (hmin : ∀ F : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F
      ∈ H →
      F • _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) ≠
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) →
      dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)) ≤
      dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
        (F • _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))) :
    ∃ K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, K ≤ H ∧ _root_.LowDimensionalTopology.Geometry.Fuchsian.IsMobiusTriangleGroup K := by
  let p := orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
  let q := orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
  have hp : 2 ≤ p := least_elliptic_realSL_order_two_le A hA hlA
  have hq : 2 ≤ q := least_elliptic_realSL_order_two_le B hB hlB
  have hsmall (n : ℕ) (hn : 2 ≤ n) : Real.pi / (n : ℝ) ∈ Ioc 0 (Real.pi / 2) := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith only [hnR]
    exact ⟨div_pos Real.pi_pos hn0, div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hnR⟩
  obtain ⟨T, ha, hc, hb, hγ, hα, htr, hgen⟩ :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_pair_actual_triangle_positive_angles A B hA hB huv hAB
      (Real.pi / p) (Real.pi / q) (hsmall p hp) (hsmall q hq)
      (by simpa only [mul_div_assoc] using haA) (by simpa only [mul_div_assoc] using haB)
  have hM : ∀ F : Matrix.SpecialLinearGroup (Fin
    2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F ∈ H →
      F • T.a ≠ T.c → dist T.c T.a ≤ dist T.c (F • T.a) := by
    intro F hFH hFne
    rw [ha, hc] at hFne ⊢
    exact hmin F hFH hFne
  have hTangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough T.b T.c
        T.b_ne_c) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough T.b T.a T.a_ne_b.symm) = T.beta :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm _ _
  have hABH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B) ∈ H := by rw [map_mul]; exact H.mul_mem hAH hBH
  obtain ⟨C, hC, hCH, hlC, hcenterC, hcut⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.minimal_center_primitive_cut_of_trace P T.b T.c T.a
      T.b_ne_c T.a_ne_b.symm (A * B) hAB hABH hb.symm (by rwa [hTangle]) hM
  have hr := least_elliptic_realSL_order_two_le C hC hlC
  rcases hcut with hfirst | ⟨hsecond, _hcollision, hrad⟩
  · have hβ : T.beta = Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) := by rwa [hTangle] at hfirst
    have ht : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsTriangleGroup (_root_.LowDimensionalTopology.Geometry.Fuchsian.triangleConformalGroup T.toClosedHTriangle) := by
      refine ⟨(q : ℕ∞), (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) : ℕ∞), (p : ℕ∞), ?_,
        ?_, ?_,
        T.toClosedHTriangle, ?_, ?_, ?_, rfl⟩
      · exact_mod_cast hq
      · exact_mod_cast hr
      · exact_mod_cast hp
      · rw [T.closed_angles.1, hα, _root_.LowDimensionalTopology.Geometry.Fuchsian.triangleOrderAngle_nat]
      · rw [T.closed_angles.2.1, hβ, _root_.LowDimensionalTopology.Geometry.Fuchsian.triangleOrderAngle_nat]
      · rw [T.closed_angles.2.2, hγ, _root_.LowDimensionalTopology.Geometry.Fuchsian.triangleOrderAngle_nat]
    refine ⟨Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup),
      (Subgroup.closure_le H).mpr ?_, native_pair_isMobiusTriangleGroup A B _ inf_le_right hgen ht⟩
    rintro f (rfl | rfl)
    · exact hAH
    · exact hBH
  · have hβ : T.beta = 2 * Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) := by rwa [hTangle] at hsecond
    obtain ⟨R, hRC, hR, hlR, hcenterR, horderR, _hcyclicR, hangleR⟩ :=
      least_elliptic_positive_orientation C hC hlC
    have hRH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R ∈ H := by
      rcases hRC with rfl | rfl
      · exact hCH
      · rw [map_inv]
        exact H.inv_mem hCH
    have hcenterRT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter R ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff R hR.1).mp hR) = T.b :=
      hcenterR.trans hcenterC
    let U := T.cyclic.cyclic
    have hUa : U.a = T.c := rfl
    have hUb : U.b = T.a := rfl
    have hUc : U.c = T.b := rfl
    have hUβ : U.beta = T.alpha := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm _ _
    have hUγ : U.gamma = T.beta := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm _ _
    have hradU : dist U.c U.a = dist U.c U.b := hrad
    have hBc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) = U.b := ha.symm
    have hRc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter R ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff R hR.1).mp hR) = U.c := hcenterRT
    have hBa : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB = 2 * U.beta := by
      rw [hUβ, hα]
      convert haB using 1
      dsimp only [q]
      ring
    have hRa : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle R hR = U.gamma := by
      rw [hUγ, hβ, ← horderR]
      exact hangleR
    have hzero := _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_isosceles_fold_product_trace_zero U hradU B R hB hR hBc hRc hBa hRa
    have hBRne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) ≠
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter R ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff R hR.1).mp hR) := by
      rw [ha.symm, hcenterRT]
      exact T.a_ne_b
    have ht := elliptic_half_turn_product_isMobiusTriangleGroup B R hB hR hBRne q
      (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)) hq (by rwa [horderR]) haB hangleR hzero
    refine ⟨Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup),
      (Subgroup.closure_le H).mpr ?_, ht⟩
    rintro f (rfl | rfl)
    · exact hBH
    · exact hRH

/-- Actual elliptic generators with a genuine elliptic product and distinct centers
force the original discrete supergroup itself to be a true triangle group. -/
theorem HalfPlaneFuchsianGroup.elliptic_product_forces_triangle
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) (hBH :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H)
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B)))
    (huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.IsMobiusTriangleGroup H := by
  obtain ⟨C, E, hC, hE, hCH, hEH, hlC, hlE, haC, haE, _hsC, _hsE, _hd, hne, hCE, hmin⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.exists_minimal_positive_elliptic_pair P A B hA hB hAH hBH hAB huv
  obtain ⟨K, hKH, ht⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.minimal_positive_elliptic_pair_contains_triangle
    P C E hC hE hCH hEH hlC hlE haC haE hne hCE hmin
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.halfPlane_supergroup_of_triangleGroup_is_triangleGroup P K hKH ht

end LowDimensionalTopology.Geometry.Fuchsian
