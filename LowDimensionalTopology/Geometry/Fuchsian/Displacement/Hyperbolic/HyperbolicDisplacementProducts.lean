/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.FuchsianCrossingHalfTurns
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeDisplacementBounds
public import Mathlib.Analysis.Real.Pi.Bounds
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Translation length is the genuine nonnegative displacement infimum. -/
theorem translationLength_nonnegative (g:ℍ≃ᵢℍ) : 0≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength g :=
  le_csInf (range_nonempty _) (by rintro _ ⟨z,rfl⟩;exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hDisplacement_nonneg g z)

theorem translation_sinh_displacement_lower (g:ℍ≃ᵢℍ) (z:ℍ) :
    Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength g/2)≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement g z := by
  have hh:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength g≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.hDisplacement g z:=
    csInf_le ⟨0,by rintro _ ⟨w,rfl⟩;exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hDisplacement_nonneg g w⟩ ⟨z,rfl⟩
  exact Real.sinh_le_sinh.mpr (by change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength g/2≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.hDisplacement g z/2;linarith only [hh])

theorem displacementP_translation_product_lower (g h:ℍ≃ᵢℍ) :
    Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength g/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength h/2)≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP g h := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_lower_bound g h _).mpr
  intro z
  exact mul_le_mul (translation_sinh_displacement_lower g z) (translation_sinh_displacement_lower h z)
    (Real.sinh_nonneg_iff.mpr (by linarith only [translationLength_nonnegative h]))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement_nonneg g z)

/-- A genuine common axis point realizes the actual product infimum. -/
theorem crossing_hyperbolic_displacementP (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A≠1) (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA:4<(Matrix.trace A.val)^2) (htB:4<(Matrix.trace B.val)^2)
    (u:ℍ) (huA:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)
    (huB:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)=
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) := by
  apply le_antisymm _ (displacementP_translation_product_lower _ _)
  have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_le (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) u
  change _≤Real.sinh (dist u (A•u)/2)*Real.sinh (dist u (B•u)/2) at hh
  rwa [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translation_minimum A hA htA u).mpr huA,
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translation_minimum B hB htB u).mpr huB] at hh

/-- Every actual axis model gives the same whole-original-disc product infimum. -/
theorem FuchsianAxisModel.displacementP {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) (M:FuchsianAxisModel D f.val) (N:FuchsianAxisModel D g.val) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementP D f g=_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry M.matrix) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry N.matrix) := by
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementP_eq_native]
  have hf:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift f)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix:=by rw [D.normalizedLift_spec,M.projection]
  have hg:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift g)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix:=by rw [D.normalizedLift_spec,N.projection]
  rw [hSLIsometry_eq_of_realSLMobius_eq _ _ hf,hSLIsometry_eq_of_realSLMobius_eq _ _ hg]

/-- The actual original product infimum for crossing original axes is attained at their intersection. -/
theorem fuchsian_crossing_displacementP {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      f.val) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val)
    (hcross:_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.AxesCross D f g hf hg) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementP D f g=Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D f/2)*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D g/2) := by
  let M:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf
  let N:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg
  obtain ⟨x,hxf,hxg⟩:=hcross
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.displacementP D f g M
    N,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.translationLength f M,
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.translationLength g N]
  exact crossing_hyperbolic_displacementP M.matrix N.matrix M.nontrivial N.nontrivial M.trace_gt
    N.trace_gt (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem M x hxf)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem N x hxg)

/-- Two genuine axis distances control the whole infimal line separation through the exact cosh identity. -/
theorem lineDist_cosh_product_lower (L M:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (z:ℍ) :
    (Real.cosh (L.lineDist M)+1)/2≤Real.cosh (L.pointDist z)*Real.cosh (M.pointDist z) := by
  have hd:=halfPlaneLine_lineDist_le_pointDist_add L M z
  have hc:Real.cosh (L.lineDist M)≤Real.cosh (L.pointDist z+M.pointDist z):=
    Real.cosh_le_cosh.mpr (by rwa [abs_of_nonneg (L.lineDist_nonneg M),
      abs_of_nonneg (add_nonneg (L.pointDist_nonneg z) (M.pointDist_nonneg z))])
  have hi:Real.cosh (L.pointDist z+M.pointDist z)+Real.cosh (L.pointDist z-M.pointDist z)=
      2*(Real.cosh (L.pointDist z)*Real.cosh (M.pointDist z)):=by
    rw [Real.cosh_add,Real.cosh_sub]
    ring
  have h1:=Real.one_le_cosh (L.pointDist z-M.pointDist z)
  linarith only [hc,hi,h1]

/-- A real metric line-separation estimate yields a bound for the actual product infimum,
without assuming simplicity or a nearest-axis normal form. -/
theorem hyperbolic_displacementP_lineDist_lower
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A≠1) (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA:4<(Matrix.trace A.val)^2) (htB:4<(Matrix.trace B.val)^2) :
    Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)*
        (Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))+1)/2≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_lower_bound _ _ _).mpr
  intro z
  have hh:=lineDist_cosh_product_lower (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
    htA) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) z
  have hs:0≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2):=by
    apply mul_nonneg <;> apply Real.sinh_nonneg_iff.mpr
    · linarith only [translationLength_nonnegative (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)]
    · linarith only [translationLength_nonnegative (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)]
  have hm:=mul_le_mul_of_nonneg_left hh hs
  change _≤Real.sinh (dist z (A•z)/2)*Real.sinh (dist z (B•z)/2)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolic_half_displacement A hA
    htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolic_half_displacement B hB htB]
  nlinarith only [hm]

/-- Exact postprocessing of the source weak separation constraint. The genuine group geometry
supplying that constraint remains a separate source obligation. -/
theorem weak_axis_separation_displacementP_quarter
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A≠1) (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA:4<(Matrix.trace A.val)^2) (htB:4<(Matrix.trace B.val)^2)
    (hsep:Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
        Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)-1/2≤
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)*
        Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))) :
    1/4≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  have hp:=hyperbolic_displacementP_lineDist_lower A B hA hB htA htB
  have hCa:=Real.one_le_cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)
  have hCb:=Real.one_le_cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)
  have hC:1≤Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
      Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2):=by nlinarith only [hCa,hCb]
  have hS:0≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2):=by
    apply mul_nonneg <;> apply Real.sinh_nonneg_iff.mpr
    · linarith only [translationLength_nonnegative (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)]
    · linarith only [translationLength_nonnegative (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)]
  nlinarith only [hp,hsep,hC,hS]

theorem cos_three_pi_div_seven_lt_quarter : Real.cos (3*Real.pi/7)<(1:ℝ)/4 := by
  have he:Real.cos (3*Real.pi/7)=Real.sin (Real.pi/14):=by
    rw [←Real.sin_pi_div_two_sub]
    congr 1
    ring
  rw [he]
  have hh:=Real.sin_lt (show 0<Real.pi/14 by positivity)
  have hp:=Real.pi_lt_d2
  linarith only [hh,hp]

end LowDimensionalTopology.Geometry.Fuchsian
