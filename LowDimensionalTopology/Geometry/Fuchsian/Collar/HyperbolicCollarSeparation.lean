/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeDisplacementBounds
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegion.CanonicalRegionFormulas
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The larger actual half-length excludes the positive trace-gap branch. -/
theorem hyperbolic_collar_positive_branch_lt_one (C S D K : ℝ)
    (hC : 0<C) (hS : 0<S) (hCS : C^2-S^2=1)
    (_hD : 0≤D) (hDC : D≤C) (hK : S*D≤K) : C*D-K<1 := by
  have hSC : S<C := by nlinarith
  have hp : 0<(C-S)*S := mul_pos (sub_pos.mpr hSC) hS
  have hm:=mul_le_mul_of_nonneg_left hDC (sub_nonneg.mpr hSC.le)
  nlinarith

/-- The two real nonelliptic product traces force the absolute geometric trace gap. -/
theorem hyperbolic_collar_logDilation_trace_gap
    (t : ℝ) (ht : 0≤t) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hp : ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t*B)))
    (hm : ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t*B⁻¹))) :
    1≤|Real.cosh t*(|B 0 0+B 1 1|/2)-Real.sinh t*(|B 0 0-B 1 1|/2)| := by
  let x:=Real.cosh t*((B 0 0+B 1 1)/2)
  let y:=Real.sinh t*((B 0 0-B 1 1)/2)
  have he : Matrix.trace (hLogDilationSL t*B).val/2=x+y := by
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
    change (Real.exp t*B 0 0+0*B 1 0+(0*B 0 1+Real.exp (-t)*B 1 1))/2=x+y
    dsimp only [x,y]
    rw [Real.cosh_eq,Real.sinh_eq]
    ring
  have hei : Matrix.trace (hLogDilationSL t*B⁻¹).val/2=x-y := by
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    change (Real.exp t*B 1 1+0*(-B 1 0)+(0*(-B 0 1)+Real.exp (-t)*B 0 0))/2=x-y
    dsimp only [x,y]
    rw [Real.cosh_eq,Real.sinh_eq]
    ring
  have hp' : 1≤|x+y| := by
    rw [←he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_not_elliptic_abs_trace (hLogDilationSL t*B) hp]
  have hm' : 1≤|x-y| := by
    rw [←hei,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_not_elliptic_abs_trace (hLogDilationSL t*B⁻¹) hm]
  have hg:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.abs_magnitudes_sub_lower_bound x y hp' hm'
  have hx : |x|=Real.cosh t*(|B 0 0+B 1 1|/2) := by
    dsimp only [x]
    rw [abs_mul,abs_div,abs_of_pos (Real.cosh_pos t)]
    norm_num
  have hy : |y|=|Real.sinh t| *(|B 0 0-B 1 1|/2) := by
    dsimp only [y]
    rw [abs_mul,abs_div]
    norm_num
  rw [hx,hy] at hg
  simpa only [abs_of_nonneg (Real.sinh_nonneg_iff.mpr ht)] using hg

/-- The normalized strong collar bound uses the genuine diagonal product sign and both actual products. -/
theorem hyperbolic_collar_logDilation_strong
    (t : ℝ) (ht : 0<t) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (had : B 0 0*B 1 1≤0) (hT : |B 0 0+B 1 1|/2≤Real.cosh t)
    (hp : ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t*B)))
    (hm : ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t*B⁻¹))) :
    1+Real.cosh t*(|B 0 0+B 1 1|/2)≤Real.sinh t*(|B 0 0-B 1 1|/2) := by
  have hdiff : |B 0 0+B 1 1|≤|B 0 0-B 1 1| := by
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs,sq_abs]
    nlinarith
  have hK:=mul_le_mul_of_nonneg_left hdiff (Real.sinh_pos_iff.mpr ht).le
  have hlt:=hyperbolic_collar_positive_branch_lt_one (Real.cosh t) (Real.sinh t)
    (|B 0 0+B 1 1|/2) (Real.sinh t*(|B 0 0-B 1 1|/2))
    (Real.cosh_pos t) (Real.sinh_pos_iff.mpr ht) (Real.cosh_sq_sub_sinh_sq t)
    (by positivity) hT (by nlinarith)
  have hg:=hyperbolic_collar_logDilation_trace_gap t ht.le B hp hm
  rcases le_abs.mp hg with he | he
  · linarith
  · linarith

/-- A genuine simple axis has a disjoint translate by any hyperbolic with a different actual axis. -/
theorem hSimple_axis_translate_disjoint_of_axes_ne
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (A B : Matrix.SpecialLinearGroup
      (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (hs : IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
      htA≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier
      ((B • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier) := by
  rcases hs.2.2 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) hBm with he | hd
  · have himage : (B • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier := by
      apply (Set.image_injective.mpr _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_injective)
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_image_realSL,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis]
      exact he
    exact False.elim (hne (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_unique_invariant B hB htB _
      himage))
  · have hdn : Disjoint ((B • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
    htA).carrier)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier := by
      simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis A hA
        htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_image_realSL,
        Set.disjoint_image_iff _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_injective] using hd
    exact hdn.symm

/-- The coefficient sign follows from actual simplicity and distinct disjoint axes alone. -/
theorem hSimple_axis0_disjoint_diagonal_nonpos
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (A B : Matrix.SpecialLinearGroup
      (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (htA : 4<(Matrix.trace A.val)^2)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1) (htB : 4<(Matrix.trace B.val)^2)
    (haxis : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
      htA=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0)
    (hs : IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) :
    B 0 0*B 1 1≤0 := by
  have hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB := by
    rw [haxis]
    exact hd.1
  have hi:=hSimple_axis_translate_disjoint_of_axes_ne G A B hA hB htA htB hs hBm hne
  rw [haxis] at hi
  have hp:=hSL_imaginaryAxis_translate_disjoint_product_nonneg B hi
  have hc:=hHyperbolic_axis0_disjoint_offdiagonal_product_neg B hB htB hd
  by_contra hn
  have hh:=mul_neg_of_pos_of_neg (lt_of_not_ge hn) hc
  linarith

/-- The strong collar inequality in the constructed diagonal model, with all signs derived from actual geometry. -/
theorem hSimple_logDilation_strong_collar
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hG :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (t : ℝ) (ht : 0<t) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htA : 4<(Matrix.trace (hLogDilationSL t).val)^2)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htB : 4<(Matrix.trace B.val)^2) (hs : IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (hLogDilationSL t)))
    (hBm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))
    (hT : Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)≤Real.cosh t) :
    1+Real.cosh t*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)≤
      Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))*
        Real.sinh t*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) := by
  have ha:=hLogDilationSL_hyperbolic_axis t ht hA htA
  have had:=hSimple_axis0_disjoint_diagonal_nonpos G (hLogDilationSL t) B hA htA hB htB ha hs hBm hd
  have hp : ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t*B)) := by
    apply hG ⟨_,?_⟩
    rw [map_mul]
    exact G.mul_mem hs.1 hBm
  have hm : ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t*B⁻¹)) := by
    apply hG ⟨_,?_⟩
    rw [map_mul,map_inv]
    exact G.mul_mem hs.1 (G.inv_mem hBm)
  have htrace : |B 0 0+B 1 1|/2=Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) := by
    simpa only [Matrix.trace_fin_two] using _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translation_abs_trace B hB htB
  have hg:=hyperbolic_collar_logDilation_strong t ht B had (by rwa [htrace]) hp hm
  rw [htrace] at hg
  have hc:=hHyperbolic_axis0_distance_translation_product B hB htB hd
  rw [←hc] at hg
  nlinarith only [hg]

/-- Two strict genuine canonical strip inequalities force the cosh of their summed point distances below the collar threshold. -/
theorem hyperbolic_collar_strip_sum (a b x y : ℝ)
    (ha : 0<a) (hb : 0<b) (hx : 0≤x) (hy : 0≤y)
    (hAx : Real.sinh x*Real.sinh a<1) (hBy : Real.sinh y*Real.sinh b<1) :
    Real.cosh (x+y)*Real.sinh a*Real.sinh b<1+Real.cosh a*Real.cosh b := by
  have hCx:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.canonical_strip_scalar x a hx ha).mpr hAx
  have hCy:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.canonical_strip_scalar y b hy hb).mpr hBy
  have hxp : 0≤Real.sinh x*Real.sinh a:=mul_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.sinh_pos_iff.mpr ha).le
  have hyp : 0≤Real.sinh y*Real.sinh b:=mul_nonneg (Real.sinh_nonneg_iff.mpr hy) (Real.sinh_pos_iff.mpr hb).le
  have hcprod : (Real.cosh x*Real.sinh a)*(Real.cosh y*Real.sinh b)<Real.cosh a*Real.cosh b :=
    mul_lt_mul hCx hCy.le (mul_pos (Real.cosh_pos y) (Real.sinh_pos_iff.mpr hb)) (Real.cosh_pos a).le
  have hsprod : (Real.sinh x*Real.sinh a)*(Real.sinh y*Real.sinh b)<1 := by
    nlinarith
  rw [Real.cosh_add]
  nlinarith only [hcprod,hsprod]

/-- The intrinsic strong axis-distance bound separates the actual canonical regions. -/
theorem hyperbolic_canonical_regions_disjoint_of_strong_axis_bound
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hstrong : 1+Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
        Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)≤
      Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA.1.1
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA)).lineDist
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB.1.1
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff B hB.1.1).mp hB)))*
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
          A)/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B) := by
  let htA:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA
  let htB:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff B hB.1.1).mp hB
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA.1.1 htA
  let M:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB.1.1 htB
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2
  have ha : 0<a:=by dsimp only [a];linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos A hA.1.1 htA]
  have hb : 0<b:=by dsimp only [b];linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos B hB.1.1 htB]
  apply Set.disjoint_left.mpr
  intro z hzA hzB
  rw [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.canonical_region_hyperbolic A hA).1] at hzA
  rw [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.canonical_region_hyperbolic B hB).1] at hzB
  change Real.sinh (L.pointDist z)*Real.sinh a<1 at hzA
  change Real.sinh (M.pointDist z)*Real.sinh b<1 at hzB
  have hp:=hyperbolic_collar_strip_sum a b (L.pointDist z) (M.pointDist z) ha hb
    Metric.infDist_nonneg Metric.infDist_nonneg hzA hzB
  have hd:=halfPlaneLine_lineDist_le_pointDist_add L M z
  have hc : Real.cosh (L.lineDist M)≤Real.cosh (L.pointDist z+M.pointDist z):=
    Real.cosh_le_cosh.mpr (by rwa [abs_of_nonneg (L.lineDist_nonneg M),abs_of_nonneg (add_nonneg (show 0≤L.pointDist z from Metric.infDist_nonneg) (show 0≤M.pointDist z from Metric.infDist_nonneg))])
  have hm:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.sinh_pos_iff.mpr ha).le)
    (Real.sinh_pos_iff.mpr hb).le
  change 1+Real.cosh a*Real.cosh b≤Real.cosh (L.lineDist M)*Real.sinh a*Real.sinh b at hstrong
  linarith

/-- The intrinsic strong collar bound for an arbitrary original simple hyperbolic map of at least the partner's translation length. -/
theorem hSimple_ordered_strong_collar
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hG :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (hs : IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))
    (hT : Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)≤Real.cosh
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)) :
    1+Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      A)/2)*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)≤
      Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))*
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) := by
  have hAH:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA).mpr htA
  obtain ⟨q,t,ht,he⟩:=realSLMobius_hyperbolic_positive_log_normal_form A hAH
  let D:=hLogDilationSL t
  let C:=q*B*q⁻¹
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) G
  have hK : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree K:=hG.conjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
  have hQH : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)) := by
    simpa only [map_mul,map_inv] using
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).mpr hAH
  have hDH : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D):=he ▸ hQH
  have hD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D≠1:=hDH.1.1
  have htD : 4<(Matrix.trace D.val)^2:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff D
    hD).mp hDH
  have hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C≠1:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation B q hB
  have htC : 4<(Matrix.trace C.val)^2 := by dsimp only [C];rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]
  have hA' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)≠1:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation A q hA
  have htA' : 4<(Matrix.trace (q*A*q⁻¹).val)^2 := by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]
  have hAD:=hHyperbolicAxis_eq_of_realSLMobius_eq (q*A*q⁻¹) D hA' hD htA' htD he
  have hDaxis:=hLogDilationSL_hyperbolic_axis t ht hD htD
  have hImageA : (q • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis D hD htD).carrier := by
    rw [←hAD,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation A q hA
      htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  have hImageB : (q • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC).carrier := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation B q hB
      htB,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  have hqpos : 0<(Matrix.SpecialLinearGroup.mapGL ℝ q).val.det := by
    change 0<q.val.det
    rw [q.det_coe]
    norm_num
  have hdis':=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
    htA).hDisjoint_realGL_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis D hD
      htD) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC)
    (Matrix.SpecialLinearGroup.mapGL ℝ q) hqpos hImageA hImageB hd
  rw [hDaxis] at hdis'
  have hsQ : IsSimple K (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)) := by
    simpa only [map_mul,map_inv] using (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_conjugation G
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).mpr hs
  have hsD : IsSimple K (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D):=he ▸ hsQ
  have hCm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈K := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) G
    rw [map_mul,map_mul,map_inv]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _
      _).mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,hBm,rfl⟩
  have hTDA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry D)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) := by
    rw [←hSLIsometry_eq_of_realSLMobius_eq _ _
      he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_translationLength_conjugation]
  have hSA : Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)=Real.sinh t := by
    rw [←hTDA]
    exact hLogDilationSL_sinh_half_translation t ht hD htD
  have hCA : Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)=Real.cosh t := by
    rw [Real.sinh_injective hSA]
  have hdist:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
    htA).lineDist_isometry_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis D hD
      htD) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC) (q • ·) (isometry_smul ℍ
      q) hImageA hImageB
  rw [hDaxis] at hdist
  have hTB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B):=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_translationLength_conjugation B q
  have hTC : Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C)/2)≤Real.cosh t := by
    rwa [hTB,←hCA]
  have hb:=hSimple_logDilation_strong_collar K hK t ht hD htD C hC htC hsD hCm hdis' hTC
  rwa [hTB,hdist,←hSA,←hCA] at hb

/-- The original simple hyperbolics with genuinely disjoint axes obey the full symmetric strong collar inequality. -/
theorem hSimple_hyperbolic_strong_collar
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hG :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (hsA : IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hsB : IsSimple G
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) :
    1+Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      A)/2)*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)≤
      Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))*
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) := by
  rcases le_total (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2))
      (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)) with hT | hT
  · exact hSimple_ordered_strong_collar G hG A B hA hB htA htB hsA hsB.1 hd hT
  · have hd' : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB
    htB).HDisjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA):=
      ⟨hd.1.symm,hd.2.1.symm,hd.2.2.symm⟩
    have hh:=hSimple_ordered_strong_collar G hG B A hB hA htB htA hsB hsA.1 hd' hT
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.lineDist_comm] at hh
    nlinarith only [hh]

/-- The actual canonical regions of two original simple hyperbolics with distinct disjoint axes are disjoint. -/
theorem canonical_simple_hyperbolic_regions_disjoint
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hG :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hsA : IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hsB : IsSimple G
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hsA.2.1.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hsA.2.1.1.1).mp
      hsA.2.1)).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hsB.2.1.1.1
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff B hsB.2.1.1.1).mp hsB.2.1))) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B) := by
  apply hyperbolic_canonical_regions_disjoint_of_strong_axis_bound A B hsA.2.1 hsB.2.1
  exact hSimple_hyperbolic_strong_collar G hG A B hsA.2.1.1.1 hsB.2.1.1.1
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hsA.2.1.1.1).mp hsA.2.1)
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff B hsB.2.1.1.1).mp
      hsB.2.1) hsA hsB hd

/-- In a genuine discrete group, hyperbolic axes sharing an ideal endpoint are the same actual axis. -/
theorem discrete_realSL_hyperbolic_axes_eq_of_shared_endpoint
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hD :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈G) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hpA :
      p∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).idealEndpoints)
    (hpB : p∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).idealEndpoints) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB := by
  have hAL:=((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA).mpr htA).1
  obtain ⟨a,b,hab,hfix⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_loxodromic_boundary_fixed_pair (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) hAL
  have hfa : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val a=a:=(hfix a).mpr (Or.inl rfl)
  have hfb : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val b=b:=(hfix b).mpr (Or.inr rfl)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints] at hpA hpB
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val p=p at hpA
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val p=p at hpB
  have hBa : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val a=a := by
    rcases (hfix p).mp hpA with hpa | hpb
    · simpa only [hpa] using hpB
    · have hBp : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val b=b:=by simpa only [hpb] using hpB
      exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_shared_loxodromic_endpoints G hD _ _ hBm hAm hAL b a hab.symm hfb hfa hBp
  have hBb : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val b=b :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_shared_loxodromic_endpoints G hD _ _ hBm hAm hAL a b hab hfa hfb hBa
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.idealEndpoints_injective
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints]
  ext w
  constructor
  · intro hw
    rcases (hfix w).mp hw with rfl | rfl
    · exact hBa
    · exact hBb
  · intro hw
    apply (hfix w).mpr
    by_cases hwa : w=a
    · exact Or.inl hwa
    by_cases hwb : w=b
    · exact Or.inr hwb
    exact False.elim (hB (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_eq_one_of_three_fixed
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) a b w hab (Ne.symm hwa) (Ne.symm hwb) hBa hBb
      hw))

/-- The source noncrossing formulation: discreteness excludes asymptotic distinct hyperbolic axes, and the actual canonical regions are disjoint. -/
theorem canonical_simple_hyperbolic_regions_disjoint_of_noncrossing
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hD :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G) (hG :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hsA : IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hsB : IsSimple G
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hsA.2.1.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hsA.2.1.1.1).mp hsA.2.1)≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hsB.2.1.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff B hsB.2.1.1.1).mp hsB.2.1))
    (hno : Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hsA.2.1.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hsA.2.1.1.1).mp
      hsA.2.1)).carrier
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hsB.2.1.1.1
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff B hsB.2.1.1.1).mp
        hsB.2.1)).carrier) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B) := by
  apply canonical_simple_hyperbolic_regions_disjoint G hG A B hsA hsB
  refine ⟨hne,Set.disjoint_left.mpr ?_,hno⟩
  intro p hpA hpB
  exact hne (discrete_realSL_hyperbolic_axes_eq_of_shared_endpoint G hD A B hsA.1 hsB.1 hsA.2.1.1.1 hsB.2.1.1.1
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hsA.2.1.1.1).mp hsA.2.1)
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff B hsB.2.1.1.1).mp
      hsB.2.1) p hpA hpB)

/-- A hyperbolic canonical region really is nonempty and cannot be disjoint from itself.
Consequently a noncrossing criterion for disjoint canonical regions must
exclude coincident axes. -/
theorem hyperbolic_canonical_region_not_disjoint_self
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    ¬Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A) := by
  let ht:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA.1.1 ht
  obtain ⟨z,hz,_⟩:=L.exists_point_ne UpperHalfPlane.I
  have hm : z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A := by
    rw [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.canonical_region_hyperbolic A hA).1]
    change Real.sinh (Metric.infDist z L.carrier)*Real.sinh _<1
    rw [Metric.infDist_zero_of_mem hz,Real.sinh_zero,zero_mul]
    norm_num
  intro hd
  exact Set.disjoint_left.mp hd hm hm

end LowDimensionalTopology.Geometry.Fuchsian
