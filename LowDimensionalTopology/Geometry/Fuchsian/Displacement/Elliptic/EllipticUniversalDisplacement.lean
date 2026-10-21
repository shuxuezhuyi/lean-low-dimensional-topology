/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticTriangleSubgroups
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticTriangleRatioBounds
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

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
theorem elliptic_pair_weighted_radial_ratio_lower
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (s t : ℝ) (hs : 0<s) (ht : 0<t)
    (hsA : s≤Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA/2))
    (htB : t≤Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2)) :
    let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
    let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
    (s*t)^2*(Real.cosh (dist u v)^2-1)/(s^2+t^2+2*s*t*Real.cosh (dist u v)) ≤
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2 := by
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
  obtain ⟨z, hz, heq⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_balanced_radial_point u v s t hs ht
  let m := s*Real.sinh (dist u z)
  have hm0 : 0≤m := mul_nonneg hs.le (Real.sinh_nonneg_iff.mpr dist_nonneg)
  have hm : m≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_lower_bound _ _ _).mpr
    intro w
    have hmin := _root_.LowDimensionalTopology.Geometry.Hyperbolic.balanced_radial_point_minimizes u v z hz s t hs.le ht.le heq w
    rw [←heq, max_self] at hmin
    refine hmin.trans (max_le_max ?_ ?_)
    · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_actual_angle_radial A hA]
      exact mul_le_mul_of_nonneg_right hsA (Real.sinh_nonneg_iff.mpr dist_nonneg)
    · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_actual_angle_radial B hB]
      exact mul_le_mul_of_nonneg_right htB (Real.sinh_nonneg_iff.mpr dist_nonneg)
  have hden : 0<s^2+t^2+2*s*t*Real.cosh (dist u v) := by positivity
  have hsum := _root_.LowDimensionalTopology.Geometry.Hyperbolic.dist_triangle_eq_of_mem_closedHSegment hz
  rw [dist_comm z v] at hsum
  have hid := _root_.LowDimensionalTopology.Geometry.Hyperbolic.balanced_sinh_square_identity s t (dist u z) (dist v
    z) heq
  rw [hsum, Real.sinh_sq] at hid
  change m^2*(s^2+t^2+2*s*t*Real.cosh (dist u v))=_ at hid
  dsimp only
  have he : (s*t)^2*(Real.cosh (dist u v)^2-1)/
      (s^2+t^2+2*s*t*Real.cosh (dist u v))=m^2 := by
    apply (div_eq_iff hden.ne').mpr
    nlinarith only [hid]
  change (s*t)^2*(Real.cosh (dist u v)^2-1)/(s^2+t^2+2*s*t*Real.cosh (dist u v))≤_
  rw [he]
  exact (sq_le_sq₀ hm0 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _)).mpr hm

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
theorem elliptic_pair_cut_displacementM_le
    (A B G K : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hG : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius G)) (hK :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius K))
    (hs : Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle G hG/2)≤Real.sin
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA/2))
    (ht : Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle K hK/2)≤Real.sin
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2))
    (hd : dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter G
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff G hG.1).mp hG))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter K
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff K hK.1).mp hK))≤
      dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry G) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry K)≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  let s := Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle G hG/2)
  let t := Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle K hK/2)
  have hspos : 0<s := Real.sin_pos_of_pos_of_lt_pi
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo G
      hG).1 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo G hG).2
  have htpos : 0<t := Real.sin_pos_of_pos_of_lt_pi
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo K
      hK).1 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo K hK).2
  have hdcosh : Real.cosh (dist
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter G
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff G hG.1).mp hG))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter K
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff K hK.1).mp hK)))≤
      Real.cosh (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))) :=
    Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg dist_nonneg] using hd)
  have hmono := _root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_radial_ratio_mono s t _ _ hspos htpos (Real.cosh_pos _).le hdcosh
  have hlow := elliptic_pair_weighted_radial_ratio_lower A B hA hB s t hspos htpos hs ht
  have hnew := _root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_pair_displacementM_square G K hG hK
  apply (sq_le_sq₀ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _)).mp
  rw [hnew]
  exact hmono.trans hlow

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
theorem elliptic_isosceles_pair_displacementM_square
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (hrad : dist T.c T.a=dist T.c T.b)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hcenterA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)=T.a)
    (hcenterB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)=T.b)
    (hangleA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA=2*T.alpha)
    (hangleB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB=2*T.beta) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2=
      (Real.cos T.beta)^2+(Real.cos (T.gamma/2))^2-1 := by
  have hbase := _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_triangle_equal_radii_base_angles T hrad
  let s := Real.sin T.beta
  let D := Real.cosh T.lengthC
  have hs : 0<s := Real.sin_pos_of_pos_of_lt_pi
    T.angles_mem_Ioo.2.1.1 T.angles_mem_Ioo.2.1.2
  have hD : 0<D := Real.cosh_pos _
  have hden : 0<s^2+s^2+2*s*s*D := by positivity
  have hm := _root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_pair_displacementM_square A B hA hB
  dsimp only at hm
  rw [hcenterA, hcenterB, hangleA, hangleB, hbase,
    show 2*T.beta/2=T.beta by ring] at hm
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2=
    (s*s)^2*(D^2-1)/(s^2+s^2+2*s*s*D) at hm
  have hreduce : (s*s)^2*(D^2-1)/(s^2+s^2+2*s*s*D)=s^2*(D-1)/2 := by
    apply (div_eq_iff hden.ne').mpr
    ring
  have hc := T.cosine_rule_II
  rw [hbase] at hc
  have hc' := (eq_div_iff (mul_ne_zero hs.ne' hs.ne')).mp hc
  change D*(s*s)=Real.cos T.beta*Real.cos T.beta+Real.cos T.gamma at hc'
  have hsrel : s^2+(Real.cos T.beta)^2=1 := Real.sin_sq_add_cos_sq T.beta
  have hcos : Real.cos T.gamma=2*(Real.cos (T.gamma/2))^2-1 := by
    simpa only [show 2*(T.gamma/2)=T.gamma by ring] using Real.cos_two_mul (T.gamma/2)
  rw [hm, hreduce]
  nlinarith only [hc', hsrel, hcos]

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
theorem HalfPlaneFuchsianGroup.minimal_positive_pair_sharp_square
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
    (4 * Real.cos (Real.pi / 7)^2 - 3) / (8 * Real.cos (Real.pi / 7) + 7) ≤
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2 := by
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
    have hs : triangleOrderAngle (p : ℕ∞) + triangleOrderAngle (q : ℕ∞) +
        triangleOrderAngle (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) : ℕ∞) < Real.pi := by
      rw [triangleOrderAngle_nat, triangleOrderAngle_nat, triangleOrderAngle_nat,
        ← hγ, ← hα, ← hβ]
      linarith only [T.angle_sum_lt_pi]
    have hsharp := _root_.LowDimensionalTopology.Geometry.Hyperbolic.ellipticTriangleRatio_sharp_lower_bound (p : ℕ∞) (q
      : ℕ∞)
      (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) : ℕ∞) (by exact_mod_cast hp) (by exact_mod_cast hq)
      (by exact_mod_cast hr) hs
    rw [triangleOrderAngle_nat, triangleOrderAngle_nat, triangleOrderAngle_nat, ← hβ] at hsharp
    have hcosβ : 0 ≤ Real.cos T.beta := by
      rw [hβ]
      simpa only [triangleOrderAngle_nat] using
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleOrderCos_mem_Icc_of_two_le (p := (orderOf
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) : ℕ∞))
          (by exact_mod_cast hr)).1
    have hD : (Real.cos (Real.pi / p) * Real.cos (Real.pi / q) + Real.cos T.beta) /
        (Real.sin (Real.pi / p) * Real.sin (Real.pi / q)) ≤
        Real.cosh (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))) := by
      rw [← hc, ← ha]
      change _ ≤ Real.cosh T.lengthB
      rw [← hγ, ← hα]
      exact le_of_eq T.cosine_rule_II_B.symm
    exact hsharp.trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_pair_order_cosine_ratio_lower A B hA
      hB hp hq _ hcosβ hD)
  · have hβ : T.beta = 2 * Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) := by rwa [hTangle] at hsecond
    let U := T.cyclic.cyclic
    have hUα : U.alpha = T.gamma := rfl
    have hUβ : U.beta = T.alpha := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm _ _
    have hUγ : U.gamma = T.beta := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm _ _
    have hradU : dist U.c U.a = dist U.c U.b := hrad
    have hAc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) = U.a := hc.symm
    have hBc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) = U.b := ha.symm
    have hAa : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA = 2 * U.alpha := by
      rw [hUα, hγ]
      convert haA using 1
      dsimp only [p]
      ring
    have hBa : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB = 2 * U.beta := by
      rw [hUβ, hα]
      convert haB using 1
      dsimp only [q]
      ring
    have hN := elliptic_isosceles_pair_displacementM_square U hradU A B hA hB hAc hBc hAa hBa
    rw [hUβ, hα, hUγ, hβ, show (2 * Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      C)) / 2 =
      Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) by ring] at hN
    have hbase := _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_triangle_equal_radii_base_angles U hradU
    have htwo : triangleOrderAngle (2 : ℕ∞) = Real.pi / 2 := by norm_num [triangleOrderAngle]
    have hs : triangleOrderAngle (q : ℕ∞) +
        triangleOrderAngle (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) : ℕ∞) +
        triangleOrderAngle (2 : ℕ∞) < Real.pi := by
      rw [triangleOrderAngle_nat, triangleOrderAngle_nat, htwo]
      have hh := U.angle_sum_lt_pi
      rw [hbase, hUβ, hα, hUγ, hβ] at hh
      rw [show 2 * Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) =
        2 * (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)) by ring] at hh
      linarith only [hh]
    have hsharp := _root_.LowDimensionalTopology.Geometry.Hyperbolic.ellipticTriangleRatio_sharp_lower_bound (q : ℕ∞)
      (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) : ℕ∞) (2 : ℕ∞) (by exact_mod_cast hq)
      (by exact_mod_cast hr) (by norm_num) hs
    rw [triangleOrderAngle_nat, triangleOrderAngle_nat, htwo, Real.cos_pi_div_two] at hsharp
    have hx : Real.cos (Real.pi / q) ∈ Icc 0 1 := by
      simpa only [triangleOrderAngle_nat] using
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleOrderCos_mem_Icc_of_two_le (p := (q : ℕ∞)) (by exact_mod_cast hq)
    have hy : Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)) ∈ Icc 0 1 := by
      simpa only [triangleOrderAngle_nat] using
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleOrderCos_mem_Icc_of_two_le (p := (orderOf
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) : ℕ∞))
          (by exact_mod_cast hr)
    have hden : 1 ≤ 2 -
        (Real.cos (Real.pi / q) - Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)))^2 := by
      nlinarith only [mul_nonneg
        (by linarith only [hx.1, hy.2] : 0 ≤ 1 + (Real.cos (Real.pi / q) -
          Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)) ))
        (by linarith only [hx.2, hy.1] : 0 ≤ 1 - (Real.cos (Real.pi / q) -
          Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)) ))]
    apply hsharp.trans
    rw [hN]
    unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.ellipticTriangleRatio
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero]
    exact div_le_self (by rw [← hN]; exact sq_nonneg _) hden

/-- The actual original pair with an elliptic product obeys the sharp universal
elliptic bound; all minimum and primitive data are derived inside the original group. -/
theorem HalfPlaneFuchsianGroup.elliptic_product_sharp_square_bound
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
    (4 * Real.cos (Real.pi / 7)^2 - 3) / (8 * Real.cos (Real.pi / 7) + 7) ≤
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2 := by
  obtain ⟨C, E, hC, hE, hCH, hEH, hlC, hlE, haC, haE, hsC, hsE, hd, hne, hCE, hmin⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.exists_minimal_positive_elliptic_pair P A B hA hB hAH hBH hAB huv
  have hbound := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.minimal_positive_pair_sharp_square P C E hC hE
    hCH hEH hlC hlE haC haE hne hCE hmin
  have hMC := elliptic_pair_cut_displacementM_le A B C E hA hB hC hE
    (by rw [least_elliptic_actual_sin_half C hC hlC]; exact hsC)
    (by rw [least_elliptic_actual_sin_half E hE hlE]; exact hsE) hd
  exact hbound.trans ((sq_le_sq₀ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _)).mpr hMC)

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
theorem native_elliptic_pair_centers_distinct
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) := by
  intro he
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  apply hNE
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_elementary_of_common_fixed _ _ ((u : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((u : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((u : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ u).mpr rfl]
  · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ((u : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((u : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff B _ u).mpr he]

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
theorem native_two_halfturn_pair_elementary
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))
    (hA2 : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) = 2) (hB2 : orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) = 2) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
  obtain ⟨L, hu, hv⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_halfPlaneLine_through u v huv
  have hAt : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt A u := ⟨hA2,
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ u).mpr rfl⟩
  have hBt : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt B v := ⟨hB2,
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff B _ v).mpr rfl⟩
  have hh := collinear_halfTurns_elementary L u v u huv hu hv hu A B A hAt hBt hAt
  have hset : ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A} : Set
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) =
      {_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} := by
    ext f
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  rwa [hset] at hh

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
theorem positive_elliptic_nonelliptic_product_ratio_lower
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hp : 2 ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hq : 2 ≤ orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (haA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA = 2 * Real.pi / orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (haB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB = 2 * Real.pi / orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))
    (hnAB : ¬ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B))) :
    (Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) + Real.cos (Real.pi
      / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)))^2 /
      (4 - (Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) -
        Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)))^2) ≤
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2 := by
  have hsep := elliptic_pair_separation_of_product_not_elliptic A B hA hB huv hnAB
  dsimp only at hsep
  rw [haA, haB, show (2 * Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) / 2 =
    Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) by ring,
    show (2 * Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) / 2 =
      Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) by ring] at hsep
  rw [add_comm] at hsep
  have hh := _root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_pair_order_cosine_ratio_lower A B hA hB hp hq 1 (by norm_num) hsep
  have he (x y : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ellipticTriangleRatio x y 1 = (x + y)^2 / (4 - (x - y)^2) := by
    unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.ellipticTriangleRatio
    congr 1 <;> ring
  rwa [he] at hh

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
theorem positive_elliptic_nonelliptic_product_sharp_square
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hp : 2 ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hq : 2 ≤ orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (haA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA = 2 * Real.pi / orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (haB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB = 2 * Real.pi / orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hnAB : ¬ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B))) :
    (4 * Real.cos (Real.pi / 7)^2 - 3) / (8 * Real.cos (Real.pi / 7) + 7) ≤
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2 := by
  have huv := native_elliptic_pair_centers_distinct A B hA hB hNE
  have hnot : ¬ ((orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) : ℕ∞) = 2 ∧ (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) : ℕ∞) = 2) := by
    intro ⟨ha, hb⟩
    have ha' : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) = 2 := by exact_mod_cast ha
    have hb' : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) = 2 := by exact_mod_cast hb
    exact hNE (native_two_halfturn_pair_elementary A B hA hB huv ha' hb')
  have hlow := _root_.LowDimensionalTopology.Geometry.Hyperbolic.ellipticNontriangleRatio_order_lower_bound (orderOf
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) : ℕ∞)
    (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) : ℕ∞) (by exact_mod_cast hp) (by exact_mod_cast hq) hnot
  rw [triangleOrderAngle_nat, triangleOrderAngle_nat] at hlow
  have hM := positive_elliptic_nonelliptic_product_ratio_lower A B hA hB hp hq haA haB huv hnAB
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ellipticTriangleSharpSquare_le_one_div_thirty_two.trans
    ((by norm_num : (1 : ℝ) / 32 ≤ 1 / 15).trans (hlow.trans hM))

/-- The sharp universal lower bound holds for every original non-elementary
elliptic pair, without primitive-angle, triangle-group, or supplied-minimum hypotheses. -/
theorem HalfPlaneFuchsianGroup.elliptic_pair_universal_sharp_square
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hgen : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) = H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) :
    (4 * Real.cos (Real.pi / 7)^2 - 3) / (8 * Real.cos (Real.pi / 7) + 7) ≤
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2 := by
  obtain ⟨C, E, hC, hE, hAC, hBE, hCEgen⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_pair_native_positive_replacements P A B hA hB hgen
  rcases hAC with ⟨hCH, hlC, haC, hcA, _hstabC, hpowC, _horderC⟩
  rcases hBE with ⟨hEH, hlE, haE, heB, _hstabE, hpowE, _horderE⟩
  have hp := least_elliptic_realSL_order_two_le C hC hlC
  have hq := least_elliptic_realSL_order_two_le E hE hlE
  have hsmall (F : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (hF : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F)) (hlF : HasLeastEllipticRotation
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F)) :
      Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F) ∈ Ioc 0 (Real.pi / 2) := by
    have hn := least_elliptic_realSL_order_two_le F hF hlF
    have hnR : (2 : ℝ) ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F) := by linarith only [hnR]
    exact ⟨div_pos Real.pi_pos hn0, div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hnR⟩
  have hsC : Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle C hC / 2) ≤
      Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2) := by
    rw [least_elliptic_actual_sin_half C hC hlC]
    exact elliptic_sin_half_lower_of_trace_bound A hA (hsmall C hC hlC)
      (least_elliptic_nonidentity_power_trace_bound C A hC hlC hA.1 hpowC)
  have hsE : Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle E hE / 2) ≤
      Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB / 2) := by
    rw [least_elliptic_actual_sin_half E hE hlE]
    exact elliptic_sin_half_lower_of_trace_bound B hB (hsmall E hE hlE)
      (least_elliptic_nonidentity_power_trace_bound E B hE hlE hB.1 hpowE)
  have hM := elliptic_pair_cut_displacementM_le A B C E hA hB hC hE hsC hsE
    (by rw [hcA, heB])
  have hNEnew : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by rwa [hCEgen]
  have hbound : (4 * Real.cos (Real.pi / 7)^2 - 3) / (8 * Real.cos (Real.pi / 7) + 7) ≤
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry E))^2 := by
    by_cases hCE : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (C * E))
    · exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_product_sharp_square_bound P C E hC hE hCH hEH hCE
        (native_elliptic_pair_centers_distinct C E hC hE hNEnew)
    · exact positive_elliptic_nonelliptic_product_sharp_square C E hC hE hp hq haC haE hNEnew hCE
  exact hbound.trans ((sq_le_sq₀ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _)).mpr hM)

/-- The universal sharp inequality, for the actual native group and metric. -/
theorem HalfPlaneFuchsianGroup.elliptic_pair_universal_sharp_bound
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hgen : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) = H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) :
    Real.sqrt ((4 * Real.cos (Real.pi / 7)^2 - 3) / (8 * Real.cos (Real.pi / 7) + 7)) ≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) :=
  Real.sqrt_le_iff.mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _,
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_pair_universal_sharp_square P A B hA hB hgen hNE⟩

/-- The first sharp inequality on the entire original invariant disc. -/
theorem fuchsian_elliptic_pair_universal_sharp_bound
    (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc (Subgroup.closure ({f, g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) (hg :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f, g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    Real.sqrt ((4 * Real.cos (Real.pi / 7)^2 - 3) / (8 * Real.cos (Real.pi / 7) + 7)) ≤
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D ⟨f, Subgroup.subset_closure (by simp)⟩
        ⟨g, Subgroup.subset_closure (by simp)⟩ := by
  obtain ⟨A, B, _hpA, _hpB, hA, hB, hgen, hM⟩ :=
    fuchsian_elliptic_pair_primitive_reduction f g D hf hg
  let P : HalfPlaneFuchsianGroup D.normalizedGroup :=
    ⟨fun k => D.normalizedGroup_preserves_halfPlane k.val k.property, D.normalizedGroup_discrete⟩
  have hNEn : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary D.normalizedGroup := hNE.conjugation D.halfPlaneNormalizer
  exact (_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_pair_universal_sharp_bound P A
    B hA hB hgen hNEn).trans hM

/--
The genuine whole-disc infimum for any original
discrete non-elementary pair has the exact universal sharp lower bound.
-/
theorem nonElementary_pair_displacement_ge_sharp_seventh_angle_constant
    (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc (Subgroup.closure ({f, g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f, g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    Real.sqrt ((4 * Real.cos (Real.pi / 7)^2 - 3) / (8 * Real.cos (Real.pi / 7) + 7)) ≤
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D ⟨f, Subgroup.subset_closure (by simp)⟩
        ⟨g, Subgroup.subset_closure (by simp)⟩ := by
  by_cases he : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g
  · exact fuchsian_elliptic_pair_universal_sharp_bound f g D he.1 he.2 hNE
  · exact fuchsian_universal_displacement_bound_of_not_two_elliptic D
      ⟨f, Subgroup.subset_closure (by simp)⟩ ⟨g, Subgroup.subset_closure (by simp)⟩ hNE he

end LowDimensionalTopology.Geometry.Fuchsian
