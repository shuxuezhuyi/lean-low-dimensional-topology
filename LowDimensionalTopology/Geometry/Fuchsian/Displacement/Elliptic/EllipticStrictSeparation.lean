/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticParabolicTriangles
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticNontriangleDisplacement
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTrianglePoincareData
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
/-- A nontriangle original group excludes both actual elliptic and actual
parabolic products of its positive primitive generators, giving strict separation. -/
theorem HalfPlaneFuchsianGroup.positive_elliptic_pair_strict_order_separation
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hlA : HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hlB : HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (haA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA = 2 * Real.pi / orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (haB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB = 2 * Real.pi / orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hgen : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) = H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hnt : ¬ IsMobiusTriangleGroup H) :
    (1 + Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) * Real.cos
      (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))) /
      (Real.sin (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) * Real.sin
        (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))) <
      Real.cosh (dist
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))) := by
  have hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H := hgen ▸ Subgroup.subset_closure (by simp)
  have hBH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H := hgen ▸ Subgroup.subset_closure (by simp)
  have hN : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by rwa [hgen]
  have huv := native_elliptic_pair_centers_distinct A B hA hB hN
  have hnE : ¬ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B)) := fun hAB =>
    hnt (_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_product_forces_triangle P A B
      hA hB hAH hBH hAB huv)
  have hnP : ¬ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B)) := by
    intro hAB
    have ht := positive_elliptic_parabolic_product_isMobiusTriangleGroup A B hA hB hlA hlB
      haA haB huv hAB
    exact hnt (hgen ▸ ht)
  have hsep := elliptic_pair_separation_of_product_not_elliptic A B hA hB huv hnE
  have hstrict := lt_of_le_of_ne hsep (fun he => hnP
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_parabolic_iff A B hA hB huv).mpr he.symm))
  change (1 + Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2) *
      Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB / 2)) /
    (Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2) * Real.sin
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB / 2)) < _
    at hstrict
  rwa [haA, haB, show (2 * Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) / 2 =
      Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) by ring,
    show (2 * Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) / 2 =
      Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) by ring] at hstrict

/-- The exact source center-separation ratio increases with the actual integer orders. -/
theorem elliptic_order_center_ratio_mono (p q P Q : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hpP : p ≤ P) (hqQ : q ≤ Q) :
    (1 + Real.cos (Real.pi / p) * Real.cos (Real.pi / q)) /
      (Real.sin (Real.pi / p) * Real.sin (Real.pi / q)) ≤
    (1 + Real.cos (Real.pi / P) * Real.cos (Real.pi / Q)) /
      (Real.sin (Real.pi / P) * Real.sin (Real.pi / Q)) := by
  have hhalf (n : ℕ) (hn : 2 ≤ n) : Real.pi / n ∈ Ioc 0 (Real.pi / 2) := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith only [hnR]
    exact ⟨div_pos Real.pi_pos hn0, div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hnR⟩
  have hangle {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) : Real.pi / N ≤ Real.pi / n := by
    have hn0 : (0 : ℝ) < n := by
      have hh : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith only [hh]
    exact div_le_div_of_nonneg_left Real.pi_pos.le hn0 (by exact_mod_cast hnN)
  have hcos {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) :
      Real.cos (Real.pi / n) ≤ Real.cos (Real.pi / N) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (hhalf N (hn.trans hnN)).1.le
      (by linarith only [(hhalf n hn).2, Real.pi_pos]) (hangle hn hnN)
  have hsin {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) :
      Real.sin (Real.pi / N) ≤ Real.sin (Real.pi / n) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith only [(hhalf N (hn.trans hnN)).1, Real.pi_pos])
      (hhalf n hn).2 (hangle hn hnN)
  have hcos0 (n : ℕ) (hn : 2 ≤ n) : 0 ≤ Real.cos (Real.pi / n) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith only [(hhalf n hn).1, Real.pi_pos]) (hhalf n hn).2
  have hsin0 (n : ℕ) (hn : 2 ≤ n) : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi (hhalf n hn).1
      (by linarith only [(hhalf n hn).2, Real.pi_pos])
  have hnum : 1 + Real.cos (Real.pi / p) * Real.cos (Real.pi / q) ≤
      1 + Real.cos (Real.pi / P) * Real.cos (Real.pi / Q) := by
    have hh := mul_le_mul (hcos hp hpP) (hcos hq hqQ)
      (hcos0 q hq) (hcos0 P (hp.trans hpP))
    linarith only [hh]
  have hden := mul_le_mul (hsin hp hpP) (hsin hq hqQ)
    (hsin0 Q (hq.trans hqQ)).le (hsin0 p hp).le
  exact (div_le_div_of_nonneg_right hnum (mul_pos (hsin0 p hp) (hsin0 q hq)).le).trans
    (div_le_div_of_nonneg_left
      (by have hh := mul_nonneg (hcos0 P (hp.trans hpP)) (hcos0 Q (hq.trans hqQ)); linarith only [hh])
      (mul_pos (hsin0 P (hp.trans hpP)) (hsin0 Q (hq.trans hqQ))) hden)

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
/--
In the actual native plane, for arbitrary original rotations
and their original orders, rather than only primitive stabilizer generators.
-/
theorem HalfPlaneFuchsianGroup.elliptic_pair_strict_order_separation
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
    (1 + Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) * Real.cos
      (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))) /
      (Real.sin (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) * Real.sin
        (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))) <
      Real.cosh (dist
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))) := by
  have hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H := hgen ▸ Subgroup.subset_closure (by simp)
  have hBH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H := hgen ▸ Subgroup.subset_closure (by simp)
  have hpA := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_realSL_order_two_le P A hA hAH
  have hqB := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_realSL_order_two_le P B hB hBH
  obtain ⟨C, E, hC, hE, hAC, hBE, hCEgen⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_pair_native_positive_replacements P A B hA hB hgen
  rcases hAC with ⟨_hCH, hlC, haC, hcA, _hstabC, _hpowC, horderC⟩
  rcases hBE with ⟨_hEH, hlE, haE, heB, _hstabE, _hpowE, horderE⟩
  have hstrict := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.positive_elliptic_pair_strict_order_separation
    P C E hC hE hlC hlE haC haE hCEgen hNE hnt
  rw [hcA, heB] at hstrict
  have hmono := elliptic_order_center_ratio_mono
    (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)) (orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E)) hpA hqB horderC horderE
  exact hmono.trans_lt hstrict

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
/--
In a nontriangle group, the hyperbolic distance between the two elliptic
fixed points strictly exceeds the lower bound determined by their orders.
-/
theorem nontriangle_elliptic_pair_cosh_center_distance_gt_order_ratio
    (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc (Subgroup.closure ({f, g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) (hg :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f, g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hnt : ¬ IsMobiusTriangleGroup (Subgroup.closure ({f, g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (x y : (fuchsianGeometricDomain D).carrier)
    (hfx : f.val x.val = x.val) (hgy : g.val y.val = y.val) :
    (1 + Real.cos (Real.pi / orderOf f) * Real.cos (Real.pi / orderOf g)) /
      (Real.sin (Real.pi / orderOf f) * Real.sin (Real.pi / orderOf g)) <
      Real.cosh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist D x y) := by
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
  have hFx : F • x = x := Subtype.ext hfx
  have hGy : G • y = y := Subtype.ext hgy
  have hx : A • _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x = _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x := by
    rw [← _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate_action, hFx]
  have hy : B • _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D y = _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D y := by
    rw [← _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate_action, hGy]
  have hcx : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) =
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x :=
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ _).mp hx).symm
  have hcy : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) =
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D y :=
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff B _ _).mp hy).symm
  have hh := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_pair_strict_order_separation P A B hA hB hgen hNEn hntn
  rw [hordA, hordB, hcx, hcy] at hh
  exact hh

end LowDimensionalTopology.Geometry.Fuchsian
