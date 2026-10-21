/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.DisjointAxisConstraints
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The diagonal difference of an actual conjugated logarithmic dilation. -/
theorem logDilation_conjugate_diagonal_difference
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ) :
    (F * hLogDilationSL t * F⁻¹) 0 0 - (F * hLogDilationSL t * F⁻¹) 1 1 =
      2 * Real.sinh t * (F 0 0 * F 1 1 + F 0 1 * F 1 0) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  change (F 0 0 * Real.exp t + F 0 1 * 0) * F 1 1 +
      (F 0 0 * 0 + F 0 1 * Real.exp (-t)) * (-F 1 0) -
    ((F 1 0 * Real.exp t + F 1 1 * 0) * (-F 0 1) +
      (F 1 0 * 0 + F 1 1 * Real.exp (-t)) * F 0 0) = _
  rw [Real.sinh_eq]
  ring

/-- The off-diagonal product of the genuine conjugated hyperbolic element. -/
theorem logDilation_conjugate_offdiagonal_product
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ) :
    (F * hLogDilationSL t * F⁻¹) 0 1 * (F * hLogDilationSL t * F⁻¹) 1 0 =
      -(4 * Real.sinh t ^ 2 * ((F 0 0 * F 1 1) * (F 0 1 * F 1 0))) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  change ((F 0 0 * Real.exp t + F 0 1 * 0) * (-F 0 1) +
      (F 0 0 * 0 + F 0 1 * Real.exp (-t)) * F 0 0) *
    ((F 1 0 * Real.exp t + F 1 1 * 0) * F 1 1 +
      (F 1 0 * 0 + F 1 1 * Real.exp (-t)) * (-F 1 0)) = _
  rw [Real.sinh_eq]
  ring

/-- Native axis separation of a logarithmic dilation and its actual conjugate
is the absolute original diagonal/off-diagonal sum. -/
theorem logDilation_axis_image_cosh
    (t : ℝ) (ht : 0 < t) (hD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t) ≠ 1)
    (htD : 4 < (Matrix.trace (hLogDilationSL t).val)^2)
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (F * hLogDilationSL t * F⁻¹)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation (hLogDilationSL t) F hD)
        (by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]))) :
    Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (F * hLogDilationSL t * F⁻¹)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation (hLogDilationSL t) F hD)
        (by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]))) =
      |F 0 0 * F 1 1 + F 0 1 * F 1 0| := by
  have he := hHyperbolic_axis0_distance_translation_product
    (F * hLogDilationSL t * F⁻¹) _ _ hd
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_translationLength_conjugation,
    hLogDilationSL_sinh_half_translation t ht hD htD,
    logDilation_conjugate_diagonal_difference, abs_mul,
    abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.sinh_pos_iff.mpr ht))] at he
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  apply (mul_right_cancel₀ hs.ne')
  convert he using 1
  ring

/-- The genuine half-separation squared has the exact determinant-one coefficient product. -/
theorem logDilation_axis_image_half_sinh_product
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) (d : ℝ)
    (hd : Real.cosh d = |F 0 0 * F 1 1 + F 0 1 * F 1 0|) :
    Real.sinh (d / 2)^2 * (Real.sinh (d / 2)^2 + 1) =
      (F 0 0 * F 1 1) * (F 0 1 * F 1 0) := by
  have hdet := F.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hdbl := Real.cosh_two_mul (d / 2)
  rw [show 2 * (d / 2) = d by ring] at hdbl
  have htrig := Real.cosh_sq_sub_sinh_sq (d / 2)
  have hsq := congrArg (fun x : ℝ => x^2) hd
  rw [sq_abs] at hsq
  nlinarith only [hdet, hdbl, htrig, hsq, sq_nonneg
    (F 0 0 * F 1 1 - F 0 1 * F 1 0 - 1)]


/-- Actual simplicity gives the native self-family noncrossing condition. -/
theorem HalfPlaneFuchsianGroup.simple_self_axis_noncrossing
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠
      1)
    (htA : 4 < (Matrix.trace A.val)^2) (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A)) :
    HyperbolicAxisFamiliesNoncrossing H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA) := by
  have hstab := ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_iff_native_axis_stable H A hA htA (fun g hg
    =>
    mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g,hg⟩))).mp hs).2
  intro F hF
  have hMap : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint ''
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).realGLMap
        (Matrix.SpecialLinearGroup.mapGL ℝ F)).carrier =
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F).val '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' ((fun z : ℍ => F • z) ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier) = _
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneSpherePoint_image_realSL F
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier).symm
  rcases hstab (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F) hF with he | hd
  · left
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneSpherePoint_injective.image_injective
    rw [hMap]
    exact he.symm
  · right
    apply (Set.disjoint_image_iff _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneSpherePoint_injective).mp
    rw [hMap]
    exact hd.symm

/-- A distinct translate of a genuine simple diagonal axis has full disjoint-line
geometry, including no common ideal endpoint. -/
theorem HalfPlaneFuchsianGroup.simple_logDilation_image_hDisjoint
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (t : ℝ) (ht : 0 < t) (hD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t) ≠ 1)
    (htD : 4 < (Matrix.trace (hLogDilationSL t).val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)))
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F ∈
      H)
    (hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (F * hLogDilationSL t * F⁻¹)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation (hLogDilationSL t) F hD)
        (by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation])) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (F * hLogDilationSL t * F⁻¹)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation (hLogDilationSL t) F hD)
        (by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation])) := by
  have haxis := hLogDilationSL_hyperbolic_axis t ht hD htD
  have hconj := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation (hLogDilationSL
    t) F hD htD
  have hno := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_self_axis_noncrossing P (hLogDilationSL t) hD htD hs
  have hne' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (hLogDilationSL t) hD htD ≠
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (hLogDilationSL t) hD htD).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ F) := by
    rw [← hconj, haxis]
    exact hne
  have hp := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.noncrossing_axis_image_hDisjoint P (hLogDilationSL t) (hLogDilationSL t)
    hs.1 hs.1 hD hD htD htD hno F hF hne'
  rwa [← hconj, haxis] at hp


/-- The genuine translated axis, expressed as the axis of the original conjugate. -/
abbrev logDilationAxisImage (t : ℝ) (hD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL
  t) ≠ 1)
    (htD : 4 < (Matrix.trace (hLogDilationSL t).val)^2)
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (F * hLogDilationSL t * F⁻¹)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation (hLogDilationSL t) F hD)
    (by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation])

/-- At an actual closest distinct translated simple axis, one genuine conjugation
and coefficient recurrence give the one-half collar estimate. -/
theorem HalfPlaneFuchsianGroup.simple_logDilation_minimum_half_sinh
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (t : ℝ) (ht : 0 < t) (hD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t) ≠ 1)
    (htD : 4 < (Matrix.trace (hLogDilationSL t).val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)))
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F ∈
      H)
    (hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 ≠ logDilationAxisImage t hD htD F)
    (hmin : ∀ Q : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Q
      ∈ H →
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 ≠ logDilationAxisImage t hD htD Q →
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist (logDilationAxisImage t hD
        htD F) ≤
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist (logDilationAxisImage t hD
          htD Q)) :
    (1 : ℝ) / 2 ≤ Real.sinh t * Real.sinh
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist (logDilationAxisImage t hD htD F) / 2) := by
  let L := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0
  let E := F * hLogDilationSL t * F⁻¹
  have hE : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E ≠ 1 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation (hLogDilationSL t) F hD
  have htE : 4 < (Matrix.trace E.val)^2 := by dsimp only [E]; rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]
  have hEm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E ∈ H := by
    dsimp only [E]
    rw [map_mul, map_mul, map_inv]
    exact H.mul_mem (H.mul_mem hF hs.1) (H.inv_mem hF)
  have hImage (Q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      (logDilationAxisImage t hD htD Q).carrier = (Q • · : ℍ → ℍ) '' L.carrier := by
    dsimp only [logDilationAxisImage]
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation (hLogDilationSL t) Q hD htD,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier,
      hLogDilationSL_hyperbolic_axis t ht hD htD]
    rfl
  have hneE : L ≠ logDilationAxisImage t hD htD E := by
    intro he
    have hinv : (E • · : ℍ → ℍ) '' L.carrier = L.carrier :=
      (hImage E).symm.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier he.symm)
    have hEq := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_unique_invariant E hE htE L hinv
    exact hne hEq
  have hdF := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_logDilation_image_hDisjoint P t ht hD htD hs F hF hne
  have hdE := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_logDilation_image_hDisjoint P t ht hD htD hs E hEm hneE
  let d := L.lineDist (logDilationAxisImage t hD htD F)
  let e := L.lineDist (logDilationAxisImage t hD htD E)
  let u := Real.sinh (d / 2)^2
  let v := Real.sinh (e / 2)^2
  have hdpos : 0 < d := L.lineDist_pos _ hdF
  have henonneg : 0 ≤ e := L.lineDist_nonneg _
  have hupos : 0 < u := sq_pos_of_pos (Real.sinh_pos_iff.mpr (by dsimp only [d]; linarith only [hdpos]))
  have hcosF : Real.cosh d = |F 0 0 * F 1 1 + F 0 1 * F 1 0| :=
    logDilation_axis_image_cosh t ht hD htD F hdF
  have hcosE : Real.cosh e = |E 0 0 * E 1 1 + E 0 1 * E 1 0| :=
    logDilation_axis_image_cosh t ht hD htD E hdE
  have hU := logDilation_axis_image_half_sinh_product F d hcosF
  change u * (u + 1) = (F 0 0 * F 1 1) * (F 0 1 * F 1 0) at hU
  have hRec := logDilation_conjugate_offdiagonal_product F t
  change E 0 1 * E 1 0 = -(4 * Real.sinh t ^ 2 * ((F 0 0 * F 1 1) * (F 0 1 * F 1 0))) at hRec
  rw [← hU] at hRec
  have hEbc : E 0 1 * E 1 0 < 0 := by
    rw [hRec]
    exact neg_neg_of_pos (by positivity)
  have hfinE : Disjoint L.carrier ((E • · : ℍ → ℍ) '' L.carrier) := by
    rw [← hImage E]
    exact hdE.2.2
  have hprodE := hSL_imaginaryAxis_translate_disjoint_product_nonneg E hfinE
  have hEad : E 0 0 * E 1 1 ≤ 0 := by
    by_contra hn
    have hbad := mul_neg_of_pos_of_neg (lt_of_not_ge hn) hEbc
    exact (not_lt_of_ge hprodE) hbad
  have hAbsE : |E 0 0 * E 1 1 + E 0 1 * E 1 0| = -(E 0 0 * E 1 1 + E 0 1 * E 1 0) :=
    abs_of_neg (by linarith only [hEad, hEbc])
  have hvRel : 2 * v + 1 = Real.cosh e := by
    have hdbl := Real.cosh_two_mul (e / 2)
    rw [show 2 * (e / 2) = e by ring] at hdbl
    have hid := Real.cosh_sq_sub_sinh_sq (e / 2)
    dsimp only [v]
    nlinarith only [hdbl, hid]
  rw [hcosE, hAbsE] at hvRel
  have hdetE := E.det_coe
  rw [Matrix.det_fin_two] at hdetE
  have hv : v = 4 * Real.sinh t ^ 2 * u * (u + 1) - 1 := by
    nlinarith only [hvRel, hdetE, hRec]
  have hde : d ≤ e := hmin E hEm hneE
  have huv : u ≤ v := by
    apply (sq_le_sq₀ (Real.sinh_nonneg_iff.mpr (by linarith only [hdpos]))
      (Real.sinh_nonneg_iff.mpr (by linarith only [henonneg]))).mpr
    exact Real.sinh_le_sinh.mpr (by linarith only [hde])
  have hfactor : 0 ≤ (u + 1) * (4 * Real.sinh t ^ 2 * u - 1) := by
    nlinarith only [huv, hv]
  have hku : 1 ≤ 4 * Real.sinh t ^ 2 * u := by
    have haux := nonneg_of_mul_nonneg_right hfactor (show 0 < u + 1 by linarith only [hupos])
    linarith only [haux]
  have hp : 0 ≤ Real.sinh t * Real.sinh (d / 2) :=
    mul_nonneg (Real.sinh_pos_iff.mpr ht).le (Real.sinh_nonneg_iff.mpr (by linarith only [hdpos]))
  change (1 : ℝ) / 2 ≤ Real.sinh t * Real.sinh (d / 2)
  dsimp only [u] at hku
  nlinarith only [hku, hp]


/-- Every distinct actual translate of an original simple diagonal axis satisfies
the one-half collar bound. The closest translate is constructed, not assumed. -/
theorem HalfPlaneFuchsianGroup.simple_logDilation_axis_collar
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (t : ℝ) (ht : 0 < t) (hD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t) ≠ 1)
    (htD : 4 < (Matrix.trace (hLogDilationSL t).val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)))
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F ∈
      H)
    (hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 ≠ logDilationAxisImage t hD htD
      F) :
    (1 : ℝ) / 2 ≤ Real.sinh t * Real.sinh
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist (logDilationAxisImage t hD htD F) / 2) := by
  let A := hLogDilationSL t
  let B := F * A * F⁻¹
  have hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ≠ 1 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation A F hD
  have htB : 4 < (Matrix.trace B.val)^2 := by dsimp only [B]; rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]
  have hBm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H := by
    dsimp only [B]
    rw [map_mul, map_mul, map_inv]
    exact H.mul_mem (H.mul_mem hF hs.1) (H.inv_mem hF)
  have haxis : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hD htD = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 :=
    hLogDilationSL_hyperbolic_axis t ht hD htD
  have haxes : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hD htD ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB := by
    rw [haxis]
    exact hne
  obtain ⟨C, hC, hneC, hminC⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.exists_closest_distinct_hyperbolic_axis_pair P A B hs.1 hBm hD hB htD htB haxes
  have hTrans (Q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB
        htB).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ Q) =
        logDilationAxisImage t hD htD (Q * F) := by
    have hm : Q * B * Q⁻¹ = (Q * F) * A * (Q * F)⁻¹ := by dsimp only [B]; group
    have he := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation B Q hB htB).symm
    simpa only [hm] using he
  have hCF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (C * F) ∈ H := by rw [map_mul]; exact H.mul_mem hC hF
  have hneCF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 ≠ logDilationAxisImage t hD htD (C * F) := by
    rwa [haxis, hTrans C] at hneC
  have hmin : ∀ Q : Matrix.SpecialLinearGroup (Fin
    2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Q ∈ H →
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 ≠ logDilationAxisImage t hD htD Q →
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist (logDilationAxisImage t hD
        htD (C * F)) ≤
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist (logDilationAxisImage t hD htD Q) := by
    intro Q hQ hneQ
    have hQF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (Q * F⁻¹) ∈ H := by
      rw [map_mul, map_inv]
      exact H.mul_mem hQ (H.inv_mem hF)
    have hQline : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB
      htB).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ (Q * F⁻¹)) =
        logDilationAxisImage t hD htD Q := by
      rw [hTrans]
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    have hQne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hD htD ≠
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ (Q * F⁻¹)) := by
      rw [haxis, hQline]
      exact hneQ
    have hm := hminC (Q * F⁻¹) hQF hQne
    rwa [haxis, hTrans C, hQline] at hm
  have hclose := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_logDilation_minimum_half_sinh
    P t ht hD htD hs (C * F) hCF hneCF hmin
  have hd := hmin F hF hne
  have hsinh := Real.sinh_le_sinh.mpr (by linarith only [hd] :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist (logDilationAxisImage t hD htD
      (C * F)) / 2 ≤
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist (logDilationAxisImage t hD
        htD F) / 2)
  exact hclose.trans (mul_le_mul_of_nonneg_left hsinh (Real.sinh_pos_iff.mpr ht).le)

end LowDimensionalTopology.Geometry.Fuchsian
