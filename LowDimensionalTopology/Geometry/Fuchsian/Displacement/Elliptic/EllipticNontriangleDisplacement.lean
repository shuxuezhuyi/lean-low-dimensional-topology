/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticUniversalDisplacement
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

/-- Finiteness and nonidentity of the actual original element follow from its
membership in the finite primitive stabilizer. -/
theorem elliptic_realSL_order_two_le_of_finite_power
    (A C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hC : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C))
    (hlC : HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C))
    (hAC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ Subgroup.zpowers
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)) :
    2 ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
  have hC2 := least_elliptic_realSL_order_two_le C hC hlC
  have hdvd := orderOf_dvd_of_mem_zpowers hAC
  have hA0 : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ≠ 0 := by
    intro hz
    rw [hz, zero_dvd_iff] at hdvd
    omega
  have hA1 : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    A) ≠ 1 := fun h => hA.1 (orderOf_eq_one_iff.mp h)
  omega

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
/-- The sharper inequality uses the orders of the original elements, even when
their rotations do not generate their full point stabilizers. -/
theorem HalfPlaneFuchsianGroup.elliptic_pair_nontriangle_square
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hgen : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) = H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hnt : ¬ IsMobiusTriangleGroup H) :
    (Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) + Real.cos (Real.pi
      / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)))^2 /
      (4 - (Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) -
        Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)))^2) ≤
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2 := by
  obtain ⟨C, E, hC, hE, hAC, hBE, hCEgen⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_pair_native_positive_replacements P A B hA hB hgen
  rcases hAC with ⟨hCH, hlC, haC, hcA, _hstabC, hpowC, horderC⟩
  rcases hBE with ⟨hEH, hlE, haE, heB, _hstabE, hpowE, horderE⟩
  have hp := least_elliptic_realSL_order_two_le C hC hlC
  have hq := least_elliptic_realSL_order_two_le E hE hlE
  have hpA := elliptic_realSL_order_two_le_of_finite_power A C hA hC hlC hpowC
  have hqB := elliptic_realSL_order_two_le_of_finite_power B E hB hE hlE hpowE
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
  have hne := native_elliptic_pair_centers_distinct C E hC hE hNEnew
  have hnCE : ¬ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (C * E)) := by
    intro hCE
    exact hnt (_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_product_forces_triangle P
      C E hC hE hCH hEH hCE hne)
  have hbound := positive_elliptic_nonelliptic_product_ratio_lower C E hC hE hp hq haC haE hne hnCE
  have hcos (n : ℕ) (hn : 2 ≤ n) : Real.cos (Real.pi / n) ∈ Icc 0 1 := by
    simpa only [triangleOrderAngle_nat] using
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleOrderCos_mem_Icc_of_two_le (p := (n : ℕ∞)) (by exact_mod_cast hn)
  have hcosAC : Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) ≤
      Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)) := by
    simpa only [triangleOrderAngle_nat] using
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleOrderCos_monotone_of_two_le
        (p := (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) : ℕ∞)) (q := (orderOf
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) : ℕ∞))
        (by exact_mod_cast hpA) (by exact_mod_cast horderC)
  have hcosBE : Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) ≤
      Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E)) := by
    simpa only [triangleOrderAngle_nat] using
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleOrderCos_monotone_of_two_le
        (p := (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) : ℕ∞)) (q := (orderOf
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E) : ℕ∞))
        (by exact_mod_cast hqB) (by exact_mod_cast horderE)
  have hmono := _root_.LowDimensionalTopology.Geometry.Hyperbolic.ellipticTriangleRatio_mono (hcos _ hpA) (hcos _ hqB) (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    (hcos _ hp) (hcos _ hq) (by norm_num : (1 : ℝ) ∈ Icc 0 1) hcosAC hcosBE le_rfl
  have he (x y : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ellipticTriangleRatio x y 1 = (x + y)^2 / (4 - (x - y)^2) := by
    unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.ellipticTriangleRatio
    congr 1 <;> ring
  simp only [he] at hmono
  exact (hmono.trans hbound).trans
    ((sq_le_sq₀ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _)).mpr hM)

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
theorem HalfPlaneFuchsianGroup.elliptic_pair_nontriangle_bound
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hgen : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) = H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hnt : ¬ IsMobiusTriangleGroup H) :
    Real.sqrt ((Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) +
      Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)))^2 /
      (4 - (Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) -
        Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)))^2)) ≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) :=
  Real.sqrt_le_iff.mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _,
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_pair_nontriangle_square P A B hA hB hgen hNE hnt⟩

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
/--
The nontriangle inequality with the literal original orders
and the whole-disc displacement infimum.
-/
theorem fuchsian_elliptic_pair_nontriangle_bound
    (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc (Subgroup.closure ({f, g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) (hg :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f, g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hnt : ¬ IsMobiusTriangleGroup (Subgroup.closure ({f, g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    Real.sqrt ((Real.cos (Real.pi / orderOf f) + Real.cos (Real.pi / orderOf g))^2 /
      (4 - (Real.cos (Real.pi / orderOf f) - Real.cos (Real.pi / orderOf g))^2)) ≤
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D ⟨f, Subgroup.subset_closure (by simp)⟩
        ⟨g, Subgroup.subset_closure (by simp)⟩ := by
  let F : Subgroup.closure ({f, g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :=
    ⟨f, Subgroup.subset_closure (by simp)⟩
  let G : Subgroup.closure ({f, g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :=
    ⟨g, Subgroup.subset_closure (by simp)⟩
  let A := D.normalizedLift F
  let B := D.normalizedLift G
  let P : HalfPlaneFuchsianGroup D.normalizedGroup :=
    ⟨fun k => D.normalizedGroup_preserves_halfPlane k.val k.property, D.normalizedGroup_discrete⟩
  have hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation f D.halfPlaneNormalizer).mpr hf
  have hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation g D.halfPlaneNormalizer).mpr hg
  have hgen : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) =
      D.normalizedGroup := (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.generated_normalized_pair D F
        G).symm
  have hNEn : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary D.normalizedGroup := hNE.conjugation D.halfPlaneNormalizer
  have hntn : ¬ IsMobiusTriangleGroup D.normalizedGroup := fun ht =>
    hnt (isMobiusTriangleGroup_of_conjugate _ D.halfPlaneNormalizer ht)
  have hordA : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) = orderOf f := by
    rw [D.normalizedLift_spec]
    exact (MulAut.conj D.halfPlaneNormalizer).orderOf_eq f
  have hordB : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) = orderOf g := by
    rw [D.normalizedLift_spec]
    exact (MulAut.conj D.halfPlaneNormalizer).orderOf_eq g
  have hbound := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_pair_nontriangle_bound P A B hA hB hgen hNEn hntn
  rw [hordA, hordB] at hbound
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM_eq_native]
  exact hbound

/-- Every actual elliptic member of the original discrete group has order at least two. -/
theorem HalfPlaneFuchsianGroup.elliptic_realSL_order_two_le
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hAH :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) :
    2 ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
  obtain ⟨C, hC, hAC⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_exists_native_positive_replacement P A hA hAH
  exact elliptic_realSL_order_two_le_of_finite_power A C hA hC hAC.2.1 hAC.2.2.2.2.2.1

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
/-- The order-dependent nontriangle bound is at least the source absolute constant. -/
theorem HalfPlaneFuchsianGroup.elliptic_pair_order_ratio_absolute_bound
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
    1 / Real.sqrt 15 ≤
      Real.sqrt ((Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) +
        Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)))^2 /
        (4 - (Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) -
          Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)))^2)) := by
  have hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H := hgen ▸ Subgroup.subset_closure (by simp)
  have hBH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H := hgen ▸ Subgroup.subset_closure (by simp)
  have hp := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_realSL_order_two_le P A hA hAH
  have hq := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_realSL_order_two_le P B hB hBH
  have hN : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by rwa [hgen]
  have hnot : ¬ ((orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) : ℕ∞) = 2 ∧ (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) : ℕ∞) = 2) := by
    intro ⟨ha, hb⟩
    have ha' : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) = 2 := by exact_mod_cast ha
    have hb' : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) = 2 := by exact_mod_cast hb
    exact hN (native_two_halfturn_pair_elementary A B hA hB
      (native_elliptic_pair_centers_distinct A B hA hB hN) ha' hb')
  simpa only [triangleOrderAngle_nat] using
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ellipticNontriangleRatio_sqrt_order_lower_bound (orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) : ℕ∞)
      (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) : ℕ∞) (by exact_mod_cast hp) (by exact_mod_cast hq) hnot

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
/--
Both inequalities in the nontriangle branch, with no
primitive-angle, minimum, order, or signature premise.
-/
theorem fuchsian_elliptic_pair_nontriangle_inequalities
    (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc (Subgroup.closure ({f, g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) (hg :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f, g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hnt : ¬ IsMobiusTriangleGroup (Subgroup.closure ({f, g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    let R := Real.sqrt ((Real.cos (Real.pi / orderOf f) + Real.cos (Real.pi / orderOf g))^2 /
      (4 - (Real.cos (Real.pi / orderOf f) - Real.cos (Real.pi / orderOf g))^2))
    1 / Real.sqrt 15 ≤ R ∧
      R ≤ _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D ⟨f, Subgroup.subset_closure (by simp)⟩
        ⟨g, Subgroup.subset_closure (by simp)⟩ := by
  refine ⟨?_, fuchsian_elliptic_pair_nontriangle_bound f g D hf hg hNE hnt⟩
  let F : Subgroup.closure ({f, g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :=
    ⟨f, Subgroup.subset_closure (by simp)⟩
  let G : Subgroup.closure ({f, g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :=
    ⟨g, Subgroup.subset_closure (by simp)⟩
  let A := D.normalizedLift F
  let B := D.normalizedLift G
  let P : HalfPlaneFuchsianGroup D.normalizedGroup :=
    ⟨fun k => D.normalizedGroup_preserves_halfPlane k.val k.property, D.normalizedGroup_discrete⟩
  have hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation f D.halfPlaneNormalizer).mpr hf
  have hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation g D.halfPlaneNormalizer).mpr hg
  have hgen : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) =
      D.normalizedGroup := (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.generated_normalized_pair D F
        G).symm
  have hNEn : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary D.normalizedGroup := hNE.conjugation D.halfPlaneNormalizer
  have hordA : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) = orderOf f := by
    rw [D.normalizedLift_spec]
    exact (MulAut.conj D.halfPlaneNormalizer).orderOf_eq f
  have hordB : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) = orderOf g := by
    rw [D.normalizedLift_spec]
    exact (MulAut.conj D.halfPlaneNormalizer).orderOf_eq g
  have hh := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_pair_order_ratio_absolute_bound P A B hA hB hgen hNEn
  simpa only [hordA, hordB] using hh

end LowDimensionalTopology.Geometry.Fuchsian
