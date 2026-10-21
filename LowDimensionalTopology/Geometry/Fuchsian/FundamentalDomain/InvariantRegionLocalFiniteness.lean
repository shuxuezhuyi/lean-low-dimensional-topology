/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.AxisTranslateLocalFiniteness
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.InvariantFundamentalRegions
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.HypercycleDistance
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HyperbolicReflectionPencils
public import Mathlib.Topology.MetricSpace.Thickening
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.ParabolicFundamentalBoundary
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.NativeParabolicPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementGeometry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane Complex.UnitDisc Pointwise OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon

/-- A genuine positive-width neighbourhood of the actual hyperbolic axis has
an actual compact period under the element's own cyclic subgroup. -/
theorem HalfPlaneFuchsianGroup.hyperbolic_axis_neighborhood_compact_core
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈
      H)
    (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2) (r :
      ℝ) :
    letI := P.nativeAction
    ∃ E : Set ℍ, IsCompact E ∧
      ∀ w ∈ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).distanceSublevel r,
        ∃ s : Subgroup.zpowers (⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hA⟩ : H),
          (s.val • ·) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf
            ht).distanceSublevel r =
            (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).distanceSublevel r ∧ w ∈ s.val • E := by
  let nativeHypercyclicCoreAction := P.nativeAction
  let : IsIsometricSMul H ℍ := ⟨fun g => (P.nativeHom g).isometry⟩
  let L := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht
  obtain ⟨C,hC,_hCL,hstable,hcover⟩ := P.hyperbolic_axis_compact_core A hA hf ht
  refine ⟨Metric.cthickening r C,hC.cthickening,?_⟩
  intro w hw
  obtain ⟨a,_b,ha,_hb,_hab⟩ := L.exists_two_points
  obtain ⟨u,hu,he⟩ := L.isClosed_carrier.exists_infDist_eq_dist ⟨a,ha⟩ w
  change Metric.infDist w L.carrier < r at hw
  rw [he] at hw
  obtain ⟨s,c,hc,hsc⟩ := hcover u hu
  refine ⟨s,L.distanceSublevel_image_isometry L _ (isometry_smul ℍ s.val) (hstable s) r,?_⟩
  have hd : dist (s.val⁻¹ • w) c < r := by
    rw [←(isometry_smul ℍ s.val).dist_eq (s.val⁻¹ • w) c,smul_inv_smul,hsc]
    exact hw
  refine ⟨s.val⁻¹ • w,?_,smul_inv_smul s.val w⟩
  exact Metric.thickening_subset_cthickening r C
    (Metric.mem_thickening_iff.mpr ⟨c,hc,hd⟩)

/-- Actual hyperbolic-axis neighbourhoods have only finitely many distinct images
meeting the closed native locally finite fundamental domain. -/
theorem HalfPlaneFuchsianGroup.hyperbolic_axis_neighborhood_images_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (D : Set ℍ) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H)
    (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2) (r :
      ℝ)
    (hLF : letI := P.nativeAction
      ∀ E : Set ℍ, IsCompact E → {g : H | (g • closure D ∩ E).Nonempty}.Finite) :
    letI := P.nativeAction
    {L : Set ℍ | ∃ g : H, L = g • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf
      ht).distanceSublevel r ∧
      (closure D ∩ L).Nonempty}.Finite := by
  let nativeHypercyclicHitAction := P.nativeAction
  let K := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).distanceSublevel r
  obtain ⟨E,hE,hcov⟩ := P.hyperbolic_axis_neighborhood_compact_core A hA hf ht r
  let F := {g : H | (g • closure D ∩ E).Nonempty}
  have hF : F.Finite := hLF E hE
  apply (hF.image (fun g : H => g⁻¹ • K)).subset
  rintro L ⟨g,rfl,x,hx,w,hw,hgw⟩
  change g • w = x at hgw
  obtain ⟨s,hs,c,hc,hsc⟩ := hcov w hw
  change s.val • c = w at hsc
  refine ⟨(g*s.val)⁻¹,?_,?_⟩
  · refine ⟨c,⟨x,hx,?_⟩,hc⟩
    change (g*s.val)⁻¹ • x = c
    rw [←hgw,←hsc,←mul_smul g s.val c,inv_smul_smul]
  · change ((g*s.val)⁻¹)⁻¹ • K = g • K
    rw [inv_inv,mul_smul]
    have hsK : s.val • K = K := hs
    rw [hsK]

/-- The positive-width axis neighbourhood also has an image meeting the actual closed fundamental domain; together these give the native-axis invariant-region conclusion. -/
theorem HalfPlaneFuchsianGroup.hyperbolic_axis_neighborhood_images_nonempty_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (D : Set ℍ) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H)
    (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2) (r :
      ℝ) (hr : 0 < r)
    (hD : letI := P.nativeAction
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ MeasureTheory.volume D)
    (hLF : letI := P.nativeAction
      ∀ E : Set ℍ, IsCompact E → {g : H | (g • closure D ∩ E).Nonempty}.Finite) :
    letI := P.nativeAction
    let T := {L : Set ℍ | ∃ g : H, L = g • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf
      ht).distanceSublevel r ∧
      (closure D ∩ L).Nonempty}
    T.Nonempty ∧ T.Finite := by
  let nativeHypercyclicPositiveAction := P.nativeAction
  refine ⟨?_,P.hyperbolic_axis_neighborhood_images_finite D A hA hf ht r hLF⟩
  let L := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht
  obtain ⟨w,_v,hw,_hv,_hne⟩ := L.exists_two_points
  have hwK : w ∈ L.distanceSublevel r := by
    change Metric.infDist w L.carrier < r
    rw [Metric.infDist_zero_of_mem hw]
    exact hr
  obtain ⟨g,hg⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.closure_meetsEveryOrbit H ℍ hD w
  exact ⟨g • L.distanceSublevel r,g,rfl,g • w,hg,w,hwK,rfl⟩

/-- A fractional-linear image of the whole vertical axis can stay in a bounded
hypercyclic strip only when both off-axis polynomial coefficients vanish. -/
theorem hypercyclic_strip_polynomial_coefficients (a b C : ℝ)
    (h : ∀ y : ℝ, 0 < y → |a*y^2+b| < C*y) : a=0 ∧ b=0 := by
  have hC : 0 < C := by
    have hh := h 1 zero_lt_one
    norm_num at hh
    exact (abs_nonneg (a+b)).trans_lt hh
  have ha : a=0 := by
    by_contra hna
    have hapos : 0 < |a| := abs_pos.mpr hna
    let y := 1+(C + |b| +1)/|a|
    have hyone : 1 < y := by
      dsimp [y]
      exact lt_add_of_pos_right _ (div_pos (by positivity) hapos)
    have hy : 0 < y := zero_lt_one.trans hyone
    have hmul : |a| *y = |a| +C + |b| +1 := by
      dsimp [y]
      field_simp
      ring
    have hh := h y hy
    have htri := abs_add_le (a*y^2+b) (-b)
    simp only [add_neg_cancel_right,abs_neg,abs_mul,abs_of_nonneg (sq_nonneg y)] at htri
    have hbmul : |b| ≤ |b| *y := by nlinarith [abs_nonneg b]
    have hineq : (|a| * y)*y < (C + |b|)*y := by nlinarith only [htri,hh,hbmul]
    have hdiv := (mul_lt_mul_iff_left₀ hy).mp hineq
    nlinarith [hdiv]
  refine ⟨ha,?_⟩
  by_contra hnb
  have hbpos : 0 < |b| := abs_pos.mpr hnb
  let y := |b|/(C+1)
  have hy : 0 < y := div_pos hbpos (by linarith)
  have hh := h y hy
  rw [ha,zero_mul,zero_add] at hh
  have heq : y*(C+1)=|b| := by dsimp [y];field_simp
  nlinarith only [hh,heq,hy]

/-- The true slope of the image of an arbitrary native imaginary-axis probe. -/
theorem realSL_imaginary_axis_slope (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (y : ℝ) (hy : 0 < y) :
    (A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy).re/(A •
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy).im =
      (A 0 0*A 1 0*y^2+A 0 1*A 1 1)/y := by
  have hdet := A.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hN := UpperHalfPlane.normSq_denom_ne_zero
    (Matrix.SpecialLinearGroup.mapGL ℝ A) (z:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy :
      ℂ))
    (by change y≠0; exact hy.ne')
  change Complex.normSq ((A 1 0 : ℂ)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy : ℂ)+(A 1 1 :
    ℂ))≠0 at hN
  change Complex.re ((A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy : ℍ) : ℂ) /
    Complex.im ((A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy : ℍ) : ℂ)=_
  simp only [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [Complex.div_re,Complex.div_im,Complex.normSq_apply,
    Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] at hN ⊢
  have hN' : A 1 1^2+A 1 0^2*y^2≠0 := by
    intro hzero
    apply hN
    nlinarith only [hzero]
  have hdet' : A 1 1*A 0 0-A 0 1*A 1 0=1 := by nlinarith only [hdet]
  field_simp [hdet',hN',hy.ne']
  rw [hdet']
  ring

/-- If all actual imaginary-axis probes have uniformly bounded distance from that
axis after a real determinant-one map, its complete axis image is the same axis. -/
theorem realSL_imaginary_axis_image_eq_of_bounded_strip
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (r : ℝ)
    (h : ∀(y : ℝ)(hy : 0<y),(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).pointDist (A •
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)<r) :
    (A • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
  have hpoly : ∀y : ℝ,0<y→|A 0 0*A 1 0*y^2+A 0 1*A 1 1|<Real.sinh r*y := by
    intro y hy
    have hh:=Real.sinh_lt_sinh.mpr (h y hy)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalLine_pointDist_sinh,sub_zero] at hh
    have hh' : |(A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy).re/(A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy).im|<Real.sinh r:=by
      simpa only [abs_div,abs_of_pos (A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y
        hy).im_pos] using hh
    rw [realSL_imaginary_axis_slope A y hy,abs_div,abs_of_pos hy] at hh'
    exact (div_lt_iff₀ hy).mp hh'
  obtain ⟨hac,hbd⟩:=hypercyclic_strip_polynomial_coefficients
    (A 0 0*A 1 0) (A 0 1*A 1 1) (Real.sinh r) hpoly
  have hsub : (A • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier⊆
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier:=by
    rintro z ⟨w,hw,rfl⟩
    have hw0 : w.re=0:=hw
    have hwProbe : w=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 w.im w.im_pos:=by
      apply UpperHalfPlane.ext
      apply Complex.ext
      · exact hw0
      · rfl
    rw [hwProbe]
    change (A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 w.im w.im_pos).re=0
    have hs:=realSL_imaginary_axis_slope A w.im w.im_pos
    rw [hac,hbd,zero_mul,zero_add,zero_div] at hs
    exact (div_eq_zero_iff.mp hs).resolve_right (A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0
      w.im w.im_pos).im_ne_zero
  obtain ⟨M,hM⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine (isometry_smul ℍ
    A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0)
  obtain ⟨p,q,hp,hq,hpq⟩:=M.exists_two_points
  have he:=M.eq_of_two_points (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0) hpq hp hq
    (hsub (hM.symm ▸hp)) (hsub (hM.symm ▸hq))
  exact hM.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier he)

/-- A real hyperbolic-plane map preserving an actual positive-width hypercyclic
region preserves its complete geometric axis, even before its type is specified. -/
theorem realSL_axis_image_eq_of_distanceSublevel_invariant
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (r :
      ℝ) (hr : 0<r)
    (hK : (A • · : ℍ→ℍ) '' L.distanceSublevel r=L.distanceSublevel r) :
    (A • · : ℍ→ℍ) '' L.carrier=L.carrier := by
  obtain ⟨g,hg,hL⟩:=L.exists_mobius_map (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0)
  let C:=g*Matrix.SpecialLinearGroup.mapGL ℝ A*g⁻¹
  have hdet : C.val.det=1:=by
    change (g.val*A.val*g⁻¹.val).det=1
    rw [Matrix.det_mul,Matrix.det_mul,A.det_coe,mul_one,←Matrix.det_mul]
    change (g*g⁻¹).val.det=1
    rw [mul_inv_cancel]
    simp
  let B : Matrix.SpecialLinearGroup (Fin 2) ℝ:=⟨C.val,hdet⟩
  have hBgl : Matrix.SpecialLinearGroup.mapGL ℝ B=C:=by
    apply Units.ext
    rfl
  have hBact (z : ℍ) : B • z=g • (A • (g⁻¹ • z)):=by
    change Matrix.SpecialLinearGroup.mapGL ℝ B • z=_
    rw [hBgl]
    change (g*Matrix.SpecialLinearGroup.mapGL ℝ A*g⁻¹) • z=_
    simp only [mul_smul]
    rfl
  have hTube:=L.distanceSublevel_image_isometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0)
    (g • ·) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g) hL r
  have hProbe (y : ℝ) (hy : 0<y) :
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).pointDist (B • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)<r:=by
    let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy
    have hz : z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier:=by change z.re=0;rfl
    obtain ⟨w,hw,hwz⟩:=hL.symm ▸hz
    have hwi : w=g⁻¹ • z:=by rw [←hwz,inv_smul_smul]
    have hwK : w∈L.distanceSublevel r:=by
      change Metric.infDist w L.carrier<r
      rw [Metric.infDist_zero_of_mem hw]
      exact hr
    have hAw : A • w∈L.distanceSublevel r:=hK ▸mem_image_of_mem _ hwK
    have hgAw : g • (A • w)∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
      0).distanceSublevel r:=
      hTube ▸mem_image_of_mem _ hAw
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).pointDist (B • z)<r
    rw [hBact,←hwi]
    exact hgAw
  have hBline:=realSL_imaginary_axis_image_eq_of_bounded_strip B r hProbe
  have himage : (g • · : ℍ→ℍ) '' ((A • · : ℍ→ℍ) '' L.carrier)=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier:=by
    rw [←hBline,←hL,image_image,image_image]
    apply image_congr
    intro z _
    rw [hBact,inv_smul_smul]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g).injective.image_injective (himage.trans
    hL.symm)

/-- Every actual hypercyclic region invariant under a genuine hyperbolic element is
a positive distance neighbourhood of that element's own actual hyperbolic axis. -/
theorem invariant_hypercyclic_region_eq_hyperbolic_axis_neighborhood
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1)
    (ht : 4<(Matrix.trace A.val)^2) (K : Set ℍ) (hK :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHHypercyclicRegion K)
    (hInv : (A • · : ℍ→ℍ) '' K=K) :
    ∃r : ℝ,0<r∧K=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).distanceSublevel r := by
  obtain ⟨L,r,hr,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.isHHypercyclicRegion_iff_distanceSublevel
    K).mp hK
  have hL:=realSL_axis_image_eq_of_distanceSublevel_invariant A L r hr hInv
  exact ⟨r,hr,congrArg (fun M : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine=>M.distanceSublevel r)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_unique_invariant A hf ht L hL)⟩

/-- An arbitrary genuine invariant hypercyclic region, with no supplied axis, has
an actual compact cyclic core in the original whole half-plane group. -/
theorem HalfPlaneFuchsianGroup.invariant_hypercyclic_region_compact_core
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H) (f :
      H)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val) (K : Set ℍ) (hK :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHHypercyclicRegion K)
    (hInv : letI := P.nativeAction;f • K=K) :
    letI := P.nativeAction
    ∃E : Set ℍ,IsCompact E∧∀w∈K,∃s : H,s • K=K∧w∈s • E := by
  let invariantHypercyclicCoreAction:=P.nativeAction
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL f.val (P.preserves f)
  have hAn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1:=hA ▸hf.1.1
  have ht : 4<(Matrix.trace A.val)^2:=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hAn).mp (hA.symm ▸hf)
  have hInvA : (A • · : ℍ→ℍ) '' K=K:=by
    have hact : (A • · : ℍ→ℍ)=(f • · : ℍ→ℍ):=by
      funext z
      exact (P.nativeAction_realSL f A hA z).symm
    rw [hact]
    exact hInv
  obtain ⟨r,hr,hKr⟩:=invariant_hypercyclic_region_eq_hyperbolic_axis_neighborhood
    A hAn ht K hK hInvA
  have hAmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H:=hA ▸f.property
  obtain ⟨E,hE,hcover⟩:=P.hyperbolic_axis_neighborhood_compact_core A hAmem hAn ht r
  refine ⟨E,hE,?_⟩
  intro w hw
  obtain ⟨s,hsK,hsw⟩:=hcover w (hKr ▸hw)
  refine ⟨s.val,?_,hsw⟩
  rw [hKr]
  exact hsK

/-- The native invariant-region conclusion for an arbitrary actual invariant region. -/
theorem HalfPlaneFuchsianGroup.invariant_hypercyclic_region_images_nonempty_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (D : Set ℍ) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val) (K : Set ℍ)
    (hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHHypercyclicRegion K) (hInv : letI := P.nativeAction;f • K=K)
    (hD : letI := P.nativeAction;_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ MeasureTheory.volume D)
    (hLF : letI := P.nativeAction
      ∀E : Set ℍ,IsCompact E→{g : H|(g • closure D∩E).Nonempty}.Finite) :
    letI := P.nativeAction
    {L : Set ℍ|∃g : H,L=g • K∧(closure D∩L).Nonempty}.Nonempty∧
      {L : Set ℍ|∃g : H,L=g • K∧(closure D∩L).Nonempty}.Finite := by
  let invariantHypercyclicImagesAction:=P.nativeAction
  obtain ⟨E,hE,hcov⟩:=P.invariant_hypercyclic_region_compact_core f hf K hK hInv
  have hFin : {L : Set ℍ|∃g : H,L=g • K∧(closure D∩L).Nonempty}.Finite:=by
    apply ((hLF E hE).image (fun g : H=>g⁻¹ • K)).subset
    rintro L ⟨g,rfl,x,hx,w,hw,hgw⟩
    change g • w=x at hgw
    obtain ⟨s,hs,c,hc,hsc⟩:=hcov w hw
    change s • c=w at hsc
    refine ⟨(g*s)⁻¹,?_,?_⟩
    · refine ⟨c,⟨x,hx,?_⟩,hc⟩
      change (g*s)⁻¹ • x=c
      rw [←hgw,←hsc,←mul_smul g s c,inv_smul_smul]
    · change ((g*s)⁻¹)⁻¹ • K=g • K
      rw [inv_inv,mul_smul,hs]
  refine ⟨?_,hFin⟩
  obtain ⟨L,r,hr,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.isHHypercyclicRegion_iff_distanceSublevel
    K).mp hK
  obtain ⟨w,v,hw,hv,hne⟩:=L.exists_two_points
  obtain ⟨g,hg⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.closure_meetsEveryOrbit H ℍ hD w
  refine ⟨g • L.distanceSublevel r,g,rfl,g • w,hg,w,?_,rfl⟩
  change Metric.infDist w L.carrier<r
  rw [Metric.infDist_zero_of_mem hw]
  exact hr

/-- The full original-disc conclusion for any actual hypercyclic region invariant
under the specified original hyperbolic element; the region's axis is not supplied. -/
theorem IsLocallyFiniteFuchsianDomain.invariant_hypercyclic_region_images_nonempty_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D K : Set P.domain.carrier} (hD : IsLocallyFiniteFuchsianDomain P D)
    (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val)
    (hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscHypercyclicRegion (P.finiteCoordinate '' K)) (hInv : f
      • K=K) :
    (fuchsianRegionImages P D K).Nonempty∧(fuchsianRegionImages P D K).Finite := by
  let E:=P.asFuchsianDisc.nielsenConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹
  have hE : E.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=cayleyInverse_unitDisc_image
  let Q:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.ofFuchsianDisc E hE
  let originalHypercyclicNativeAction:=Q.nativeAction
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ H
  let ψ:=P.halfPlaneCoordinate
  have hCoord (g : H) (S : Set P.domain.carrier) : ψ '' (g • S)=e g • (ψ '' S):=by
    change ψ '' ((g • ·) '' S)=(e g • ·) '' (ψ '' S)
    rw [image_image,image_image]
    apply image_congr
    intro x _
    exact (unitDisc_halfPlaneConjugate_nativeAction P g x).symm
  have hCK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' (ψ '' K)=P.finiteCoordinate '' K:=by
    rw [image_image]
    apply image_congr
    intro x _
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane (P.finiteCoordinate x)
  have hKH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHHypercyclicRegion (ψ '' K):=by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isDiscHypercyclicRegion_cayley_iff _).mp
    rwa [hCK]
  have hfH : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (e f).val:=by
    change _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*f.val*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹)⁻¹)
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward f.val _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ hf
  have hInvH : e f • (ψ '' K)=ψ '' K:=by rw [←hCoord,hInv]
  obtain ⟨C,hC,hcover⟩:=Q.invariant_hypercyclic_region_compact_core (e f) hfH
    (ψ '' K) hKH hInvH
  have hcoverOriginal : ∀w∈K,∃s : H,s • K=K∧w∈s • (ψ.symm '' C):=by
    intro w hw
    obtain ⟨s,hs,c,hc,hsc⟩:=hcover (ψ w) (mem_image_of_mem ψ hw)
    change s • c=ψ w at hsc
    refine ⟨e.symm s,?_,ψ.symm c,mem_image_of_mem _ hc,?_⟩
    · apply ψ.injective.image_injective
      rw [hCoord,e.apply_symm_apply,hs]
    · change e.symm s • ψ.symm c=w
      apply ψ.injective
      rw [←unitDisc_halfPlaneConjugate_nativeAction P (e.symm s) (ψ.symm c),
        e.apply_symm_apply,ψ.apply_symm_apply,hsc]
  have hFin:=hD.region_images_finite_of_compact_cover (hC.image ψ.symm.continuous) hcoverOriginal
  refine ⟨hD.fundamental.regionImages_nonempty ?_,hFin⟩
  obtain ⟨L,r,hr,hKr⟩:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.isHHypercyclicRegion_iff_distanceSublevel (ψ
    '' K)).mp hKH
  obtain ⟨p,q,hp,hq,hpq⟩:=L.exists_two_points
  have hpK : p∈ψ '' K:=by
    rw [hKr]
    change Metric.infDist p L.carrier<r
    rw [Metric.infDist_zero_of_mem hp]
    exact hr
  obtain ⟨w,hw,_⟩:=hpK
  exact ⟨w,hw⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Every literal unit complex multiplier is the actual disc action of a real SL rotation. -/
theorem unit_disc_rotation_exists_realSL (ζ : ℂ) (hζ : ‖ζ‖=1) :
    ∃A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀z : 𝔻,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action A z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation ζ hζ z := by
  obtain ⟨u,hu⟩:=IsAlgClosed.exists_pow_nat_eq ζ (by norm_num : 0<(2 : ℕ))
  have hn : ‖u‖=1:=by
    have he:=congrArg norm hu
    rw [norm_pow,hζ] at he
    nlinarith [norm_nonneg u]
  have hparam : u.re^2+u.im^2=1:=by
    have he : Complex.normSq u=1:=by rw [Complex.normSq_eq_norm_sq,hn,one_pow]
    rw [Complex.normSq_apply] at he
    nlinarith only [he]
  have hmult : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationMultiplier u.re u.im=ζ:=by
    change u/conj u=ζ
    apply (div_eq_iff (norm_ne_zero_iff.mp (by rw [Complex.norm_conj,hn];norm_num))).mpr
    rw [←hu]
    calc
      u=u*(u*conj u):=by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.unit_mul_conj_eq_one u hn,mul_one]
      _=u^2*conj u:=by ring
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL u.re u.im hparam,?_⟩
  intro z
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL_disc_action]
  apply Subtype.ext
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationMultiplier u.re u.im*(z : ℂ)=ζ*(z : ℂ)
  rw [hmult]

/-- The literal tangent circle region rotates to the corresponding literal tangent circle region. -/
theorem discHorocyclicRegion_rotation_image (ζ : ℂ) (hζ : ‖ζ‖=1) (r : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation ζ hζ '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHorocyclicRegion 1 r=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHorocyclicRegion ζ r := by
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotationHomeomorph ζ hζ
  have he:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHorocyclicRegion_eq_rotation_preimage ζ hζ r
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHorocyclicRegion ζ r=F.symm ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHorocyclicRegion 1 r at he
  exact (F.toEquiv.image_eq_preimage_symm _).trans he.symm

/-- Every actual horocyclic region is an actual real-SL image of a positive horizontal region. -/
theorem horocyclic_region_exists_realSL_horizontal_image {K : Set ℍ}
    (hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHHorocyclicRegion K) :
    ∃(A : Matrix.SpecialLinearGroup (Fin 2) ℝ)(k : ℝ),0<k∧
      K=(A • · : ℍ→ℍ) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k := by
  obtain ⟨ζ,hζ,r,hr,hr1,hR⟩:=hK
  obtain ⟨A,hA⟩:=unit_disc_rotation_exists_realSL ζ hζ
  refine ⟨A,(1-r)/r,div_pos (sub_pos.mpr hr1) hr,?_⟩
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective.image_injective
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' K=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' ((A • · : ℍ→ℍ) '' _)
  rw [hR,←discHorocyclicRegion_rotation_image ζ hζ r,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHorocyclicRegion_one_eq_cayley_image r hr hr1,image_image,image_image]
  apply image_congr
  intro z _
  exact (hA (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)).symm.trans
    (by change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))=_;
        rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc])

/-- A real-SL map fixing infinity carries each positive horizontal region to another one. -/
theorem realSL_fix_infty_horizontal_region_image
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A).val ∞=∞)
    (k : ℝ) (hk : 0<k) :
    ∃t : ℝ,0<t∧(A • · : ℍ→ℍ) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k=_root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion t := by
  have hc:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff A).mp hA
  have hd : A 1 1≠0:=by
    intro hzero
    have hdet:=A.det_coe
    rw [Matrix.det_fin_two,hc,hzero] at hdet
    norm_num at hdet
  have hs : ∀z : ℍ,(A • z).im=z.im/(A 1 1)^2:=by
    intro z
    rw [realSL_im_action]
    congr 1
    change Complex.normSq ((A 1 0 : ℂ)*(z : ℂ)+(A 1 1 : ℂ))=(A 1 1)^2
    simp only [hc,Complex.ofReal_zero,zero_mul,zero_add,Complex.normSq_ofReal,pow_two]
  refine ⟨k/(A 1 1)^2,div_pos hk (sq_pos_of_ne_zero hd),?_⟩
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    change k/(A 1 1)^2<(A • w).im
    rw [hs]
    exact (div_lt_div_iff_of_pos_right (sq_pos_of_ne_zero hd)).mpr hw
  · intro hz
    refine ⟨A⁻¹ • z,?_,smul_inv_smul A z⟩
    have he:=hs (A⁻¹ • z)
    rw [smul_inv_smul] at he
    change k<(A⁻¹ • z).im
    change k/(A 1 1)^2<z.im at hz
    rw [he] at hz
    exact (div_lt_div_iff_of_pos_right (sq_pos_of_ne_zero hd)).mp hz

/-- The specified original parabolic's arbitrary invariant horocyclic region is
horizontal in a genuine whole-group unit-translation chart. Its ideal center and
the positive height are derived from the original region, not added as hypotheses. -/
theorem UnitDiscFuchsianGroup.invariant_horocyclic_region_normalized
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) (K : Set P.domain.carrier)
    (hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscHorocyclicRegion (P.finiteCoordinate '' K)) (hInv : f
      • K=K) :
    ∃(q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)(A : Matrix.SpecialLinearGroup (Fin 2) ℝ)(t :
      ℝ),
      q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet∧_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H∧0<t∧
      K=P.halfPlaneCoordinate.symm '' ((fordSLNativeHom A).symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion t) := by
  let ψ:=P.halfPlaneCoordinate
  have hCK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' (ψ '' K)=P.finiteCoordinate '' K:=by
    rw [image_image]
    apply image_congr
    intro x _
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane (P.finiteCoordinate x)
  have hKH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHHorocyclicRegion (ψ '' K):=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscHorocyclicRegion (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' (ψ '' K))
    rwa [hCK]
  obtain ⟨N,k,hk,hNK⟩:=horocyclic_region_exists_realSL_horizontal_image hKH
  obtain ⟨B,hB,hAct⟩:=P.halfPlaneAction_real_lift f
  have hInvB : (B • · : ℍ→ℍ) '' (ψ '' K)=ψ '' K:=by
    calc
      _=ψ '' (f • K):=by
        change (B • ·) '' (ψ '' K)=ψ '' ((f • ·) '' K)
        rw [image_image,image_image]
        apply image_congr
        intro x _
        exact (hAct (ψ x)).trans (P.halfPlaneAction_coordinate f x)
      _=ψ '' K:=by rw [hInv]
  have hBN : ((B*N) • · : ℍ→ℍ) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k=
      (N • · : ℍ→ℍ) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k:=by
    simpa only [hNK,image_image,mul_smul] using hInvB
  have hFixN:=realSL_horocyclic_image_eq_endpoint (B*N) N k hk hBN
  rw [map_mul] at hFixN
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    B).val ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N).val
    ∞)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N).val ∞ at hFixN
  let ξ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N).val ∞)
  have hFix : f.val.val ξ=ξ:=by
    have hGroup : f.val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹:=by rw [hB];group
    rw [hGroup]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N).val ∞))))=ξ
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm_apply_apply,hFixN]
  obtain ⟨q,hq,hT,hqξ⟩:=parabolic_unit_halfPlane_normalizer P f hf ξ hFix
  obtain ⟨A,hA⟩:=halfPlane_chart_real_lift q hq
  have hAN : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*N)).val ∞=∞:=by
    rw [map_mul,hA]
    exact hqξ
  obtain ⟨t,ht,hImage⟩:=realSL_fix_infty_horizontal_region_image (A*N) hAN k hk
  let F:=fordSLNativeHom A
  have hNormalized : F '' (ψ '' K)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion t:=by
    rw [hNK,image_image]
    change (fun z : ℍ=>A • (N • z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k=_
    simpa only [mul_smul] using hImage
  refine ⟨q,A,t,hq,hA,hT,ht,?_⟩
  calc
    K=ψ.symm '' (F.symm '' (F '' (ψ '' K))):=by
      simp only [image_image,F.symm_apply_apply,ψ.symm_apply_apply,image_id']
    _=ψ.symm '' (F.symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion t):=by rw [hNormalized]

/--
For every original invariant horocyclic region, without
a supplied center, normalized-family hypothesis or chosen height.
-/
theorem IsLocallyFiniteFuchsianDomain.invariant_horocyclic_region_images_nonempty_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D K : Set P.domain.carrier} (hD : IsLocallyFiniteFuchsianDomain P D)
    (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscHorocyclicRegion (P.finiteCoordinate '' K)) (hInv : f
      • K=K) :
    (fuchsianRegionImages P D K).Nonempty∧(fuchsianRegionImages P D K).Finite := by
  obtain ⟨q,A,t,hq,hA,hT,ht,hShape⟩:=P.invariant_horocyclic_region_normalized f hf K hK hInv
  rw [hShape]
  refine ⟨hD.fundamental.regionImages_nonempty ?_,
    hD.halfPlane_chart_horocyclic_images_finite q hq A hA hT t ht⟩
  refine ⟨P.halfPlaneCoordinate.symm ((fordSLNativeHom A).symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (t+1) (by linarith))),?_⟩
  exact ⟨_,⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (t+1) (by linarith),by change t<t+1;linarith,rfl⟩,rfl⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces

/--
Only finitely many translates of a nonempty compact set, or of a specified
invariant horocyclic or hypercyclic region, meet the closed fundamental domain.
The compact case also covers regions invariant under an elliptic element.
-/
theorem compact_horocyclic_hypercyclic_regionImages_nonempty_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsLocallyFiniteFuchsianDomain P D) :
    (∀K : Set P.domain.carrier,IsCompact K→K.Nonempty→
      (fuchsianRegionImages P D K).Nonempty∧(fuchsianRegionImages P D K).Finite)∧
    (∀f : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val→∀K : Set P.domain.carrier,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscHorocyclicRegion (P.finiteCoordinate '' K)→f • K=K→
      (fuchsianRegionImages P D K).Nonempty∧(fuchsianRegionImages P D K).Finite)∧
    (∀f : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val→∀K : Set P.domain.carrier,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscHypercyclicRegion (P.finiteCoordinate '' K)→f • K=K→
      (fuchsianRegionImages P D K).Nonempty∧(fuchsianRegionImages P D K).Finite) := by
  refine ⟨fun K hK hn=>compact_nonempty_regionImages_nonempty_finite hD hK hn,?_,?_⟩
  · intro f hf K hK hInv
    exact hD.invariant_horocyclic_region_images_nonempty_finite f hf hK hInv
  · intro f hf K hK hInv
    exact hD.invariant_hypercyclic_region_images_nonempty_finite f hf hK hInv

end LowDimensionalTopology.Geometry.Fuchsian
