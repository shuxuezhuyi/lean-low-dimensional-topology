/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.HyperbolicPencilTransport
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.EllipticPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.ParabolicPencilTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The complete genuine displacement level containing a specified actual point. -/
def hDisplacementLevel (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℍ) : Set ℍ :=
  {z | dist z (A • z)=dist w (A • w)}

theorem hDisplacementLevel_conjugation (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℍ) :
    hDisplacementLevel (q*A*q⁻¹) (q • w)=(q • · : ℍ→ℍ) '' hDisplacementLevel A w := by
  ext z
  constructor
  · intro hz
    refine ⟨q⁻¹ • z,?_,by simp⟩
    change dist _ _=dist _ _ at hz ⊢
    have hd:=(isometry_smul ℍ q).dist_eq (q⁻¹ • z) (A • (q⁻¹ • z))
    simp only [smul_inv_smul] at hd
    have hw:=(isometry_smul ℍ q).dist_eq w (A • w)
    simp only [mul_smul,inv_smul_smul] at hz
    exact hd.symm.trans (hz.trans hw)
  · rintro ⟨v,hv,rfl⟩
    change dist _ _=dist _ _ at hv ⊢
    simpa only [mul_smul,inv_smul_smul] using
      ((isometry_smul ℍ q).dist_eq v (A • v)).trans
        (hv.trans ((isometry_smul ℍ q).dist_eq w (A • w)).symm)

/-- Elliptic displacement levels are precisely the genuine metric-radius levels about the actual center. -/
theorem hDisplacementLevel_elliptic (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (w : ℍ) :
    hDisplacementLevel A w=hMetricCircle
      (hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA))
      (dist w (hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA))) := by
  obtain ⟨a,b,_hu,hb,hdisp,_hconj⟩:=elliptic_half_displacement A hA
  ext z
  change dist z (A • z)=dist w (A • w) ↔ _=_
  constructor
  · intro he
    have hs:=congrArg (fun t : ℝ=>Real.sinh (t/2)) he
    rw [hdisp,hdisp] at hs
    exact Real.sinh_injective (mul_right_cancel₀ (abs_ne_zero.mpr hb) hs)
  · intro he
    have hs : Real.sinh (dist z (A • z)/2)=Real.sinh (dist w (A • w)/2) := by
      rw [hdisp,hdisp,he]
    linarith [Real.sinh_injective hs]

/-- The elliptic minimum is the actual singleton center; all other levels are regular metric circles. -/
theorem hDisplacementLevel_elliptic_regular_or_center
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : Mobius.MobiusElliptic (realSLMobius A)) (w : ℍ) :
    let v:=hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    (w=v ∧ hDisplacementLevel A w={v}) ∨
      (w≠v ∧ hDisplacementLevel A w∈hMetricCircleFamily v) := by
  dsimp only
  rw [hDisplacementLevel_elliptic A hA w]
  by_cases he : w=hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
  · left
    refine ⟨he,?_⟩
    rw [he,dist_self,hMetricCircle_zero]
  · exact Or.inr ⟨he,_,dist_pos.mpr he,rfl⟩

/-- Hyperbolic displacement levels are exactly full distance levels of the actual invariant geodesic. -/
theorem hDisplacementLevel_hyperbolic (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A≠1) (ht : 4<(Matrix.trace A.val)^2) (w : ℍ) :
    hDisplacementLevel A w={z | (hHyperbolicAxis A hA ht).pointDist z=
      (hHyperbolicAxis A hA ht).pointDist w} := by
  have hpos : 0<Real.sinh (hTranslationLength (hSLIsometry A)/2) :=
    Real.sinh_pos_iff.mpr (by linarith [hHyperbolic_translationLength_pos A hA ht])
  ext z
  change dist z (A • z)=dist w (A • w) ↔ _=_
  constructor
  · intro he
    have hs:=congrArg (fun t : ℝ=>Real.sinh (t/2)) he
    rw [hyperbolic_half_displacement A hA ht,hyperbolic_half_displacement A hA ht] at hs
    have hc:=mul_right_cancel₀ hpos.ne' hs
    exact Real.cosh_strictMonoOn.injOn
      ((hHyperbolicAxis A hA ht).pointDist_nonneg z)
      ((hHyperbolicAxis A hA ht).pointDist_nonneg w) hc
  · intro he
    have hs : Real.sinh (dist z (A • z)/2)=Real.sinh (dist w (A • w)/2) := by
      rw [hyperbolic_half_displacement A hA ht,hyperbolic_half_displacement A hA ht,he]
    linarith [Real.sinh_injective hs]

/-- Every positive hyperbolic displacement level splits into exactly two distinct disjoint actual branches. -/
theorem hDisplacementLevel_hyperbolic_two_branches (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A≠1) (ht : 4<(Matrix.trace A.val)^2) (w : ℍ)
    (hw : 0<(hHyperbolicAxis A hA ht).pointDist w) :
    ∃S T : Set ℍ,IsHHypercycleBranch (hHyperbolicAxis A hA ht) S ∧
      IsHHypercycleBranch (hHyperbolicAxis A hA ht) T ∧ Disjoint S T ∧ S≠T ∧
      hDisplacementLevel A w=S∪T := by
  rw [hDisplacementLevel_hyperbolic A hA ht w]
  exact (hHyperbolicAxis A hA ht).distance_level_two_hypercycleBranches _ hw

/-- Changing the sign of a real SL representative does not change a displacement level. -/
theorem hDisplacementLevel_neg (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℍ) :
    hDisplacementLevel (-A) w=hDisplacementLevel A w := by
  ext z
  simp only [hDisplacementLevel,mem_ofPred_eq,hSL_neg_smul]

/-- The genuine displacement levels of a nontrivial standard translation are all horizontal horocycles. -/
theorem hDisplacementLevel_translation (t : ℝ) (ht : t≠0) (w : ℍ) :
    hDisplacementLevel (hTranslationSL t) w=horizontalHorocycle w.im := by
  ext z
  change dist z (hTranslationSL t • z)=dist w (hTranslationSL t • w) ↔ z.im=w.im
  constructor
  · intro he
    have hs:=congrArg (fun s : ℝ=>Real.sinh (s/2)) he
    rw [translation_half_displacement,translation_half_displacement] at hs
    have hh:=(div_eq_div_iff (by positivity : (2:ℝ)*z.im≠0)
      (by positivity : (2:ℝ)*w.im≠0)).mp hs
    nlinarith [abs_pos.mpr ht]
  · intro he
    have hs : Real.sinh (dist z (hTranslationSL t • z)/2)=
        Real.sinh (dist w (hTranslationSL t • w)/2) := by
      rw [translation_half_displacement,translation_half_displacement,he]
    linarith [Real.sinh_injective hs]

/-- A genuine real normalizer simultaneously puts every parabolic displacement level into its actual horocycle chart. -/
theorem hDisplacementLevel_parabolic_normalizer (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) :
    ∃q : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (realSLMobius A).val ((realSLMobius q⁻¹).val ∞)=(realSLMobius q⁻¹).val ∞ ∧
      ∀w : ℍ,hDisplacementLevel A w=
        (q⁻¹ • · : ℍ→ℍ) '' horizontalHorocycle (q • w).im := by
  obtain ⟨q,t,ht,he⟩:=realSLMobius_parabolic_normal_form A hA
  refine ⟨q,?_,?_⟩
  · have hT : (realSLMobius (q*A*q⁻¹)).val ∞=∞ := by
      rcases he with he | he
      · rw [he]
        exact (realSLMobius_fixed_infty_iff _).mpr rfl
      · rw [he,realSLMobius_neg]
        exact (realSLMobius_fixed_infty_iff _).mpr rfl
    apply (realSLMobius_conjugate_fixed_iff A q _).mp
    have hqw : (realSLMobius q).val ((realSLMobius q⁻¹).val ∞)=∞ := by
      rw [map_inv]
      exact Equiv.apply_symm_apply _ _
    rwa [hqw]
  · intro w
    have himage : (q • · : ℍ→ℍ) '' hDisplacementLevel A w=horizontalHorocycle (q • w).im := by
      rw [←hDisplacementLevel_conjugation A q w]
      rcases he with he | he
      · rw [he,hDisplacementLevel_translation t ht]
      · rw [he,hDisplacementLevel_neg,hDisplacementLevel_translation t ht]
    have hb:=congrArg (fun S : Set ℍ=>(q⁻¹ • · : ℍ→ℍ) '' S) himage
    simpa only [image_image,inv_smul_smul,image_id'] using hb

/-- Each full parabolic displacement level is a genuine generalized-circle horocycle at its actual fixed ideal point. -/
theorem hDisplacementLevel_parabolic (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) :
    ∃v : Mobius.ExtendedComplex,(realSLMobius A).val v=v ∧
      ∀w : ℍ,IsHHorocycleAt v (hDisplacementLevel A w) := by
  obtain ⟨q,hq,hlevel⟩:=hDisplacementLevel_parabolic_normalizer A hA
  refine ⟨(realSLMobius q⁻¹).val ∞,hq,?_⟩
  intro w
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ q⁻¹
  have hg : 0<g.val.det := by change 0<(q⁻¹).val.det;rw [(q⁻¹).det_coe];norm_num
  have hS:=(horizontalHorocycle_isHHorocycleAt (q • w).im (q • w).im_pos).realGL_image g hg
  have hw : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞=(realSLMobius q⁻¹).val ∞ := by
    rw [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,realSLMobius_matrix]
  rw [hw] at hS
  rw [hlevel]
  exact hS

/-- Every positive genuine metric circle about the actual elliptic center occurs as a full displacement level. -/
theorem hMetricCircle_is_elliptic_displacementLevel
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : Mobius.MobiusElliptic (realSLMobius A))
    (r : ℝ) (hr : 0≤r) :
    ∃w : ℍ,hDisplacementLevel A w=
      hMetricCircle (hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)) r := by
  obtain ⟨w,hw⟩:=hMetricCircle_nonempty
    (hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)) r hr
  refine ⟨w,?_⟩
  rw [hDisplacementLevel_elliptic A hA w]
  exact congrArg (hMetricCircle _) hw

/-- All genuine horocycles at the unique parabolic ideal point, and only those, are full displacement levels. -/
theorem isHHorocycle_iff_parabolic_displacementLevel
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : Mobius.MobiusParabolic (realSLMobius A)) :
    ∃v : Mobius.ExtendedComplex,(realSLMobius A).val v=v ∧
      ∀S : Set ℍ,IsHHorocycleAt v S ↔ ∃w : ℍ,S=hDisplacementLevel A w := by
  obtain ⟨v,hv,hlevel⟩:=hDisplacementLevel_parabolic A hA
  refine ⟨v,hv,?_⟩
  intro S
  constructor
  · intro hS
    obtain ⟨w,hw⟩:=hS.choose_spec.2.2
    obtain ⟨T,_hT,hunique⟩:=existsUnique_hHorocycleAt_through v
      (realSLMobius_parabolic_fixed_boundary A hA v hv) w
    refine ⟨w,(hunique S ⟨hS,hw⟩).trans (hunique _ ⟨hlevel w,rfl⟩).symm⟩
  · rintro ⟨w,rfl⟩
    exact hlevel w

/-- On the actual invariant geodesic the complete hyperbolic minimum level is exactly that geodesic. -/
theorem hDisplacementLevel_hyperbolic_axis (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A≠1) (ht : 4<(Matrix.trace A.val)^2) (w : ℍ)
    (hw : w∈(hHyperbolicAxis A hA ht).carrier) :
    hDisplacementLevel A w=(hHyperbolicAxis A hA ht).carrier := by
  let L:=hHyperbolicAxis A hA ht
  obtain ⟨u,v,hu,_hv,_hne⟩:=L.exists_two_points
  have he : ∀z : ℍ,L.pointDist z=0 ↔ z∈L.carrier := by
    intro z
    exact (L.isClosed_carrier.mem_iff_infDist_zero ⟨u,hu⟩).symm
  rw [hDisplacementLevel_hyperbolic A hA ht w]
  have hw0 : L.pointDist w=0:=(he w).mpr hw
  change {z : ℍ | L.pointDist z=L.pointDist w}=L.carrier
  rw [hw0]
  exact Set.ext (fun z=>he z)

/-- Every actual individual complementary hypercycle branch is contained in the full displacement level through each of its points. -/
theorem hHypercycleBranch_subset_displacementLevel
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1)
    (ht : 4<(Matrix.trace A.val)^2) {S : Set ℍ}
    (hS : IsHHypercycleBranch (hHyperbolicAxis A hA ht) S) {w : ℍ} (hw : w∈S) :
    S⊆hDisplacementLevel A w := by
  rw [hDisplacementLevel_hyperbolic A hA ht w]
  intro z hz
  exact hS.pointDist_eq hz hw

/-- The complete hyperbolic level classification includes both its true minimum geodesic and its two regular branches. -/
theorem hDisplacementLevel_hyperbolic_axis_or_two_branches
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1)
    (ht : 4<(Matrix.trace A.val)^2) (w : ℍ) :
    hDisplacementLevel A w=(hHyperbolicAxis A hA ht).carrier ∨
      ∃S T : Set ℍ,IsHHypercycleBranch (hHyperbolicAxis A hA ht) S ∧
        IsHHypercycleBranch (hHyperbolicAxis A hA ht) T ∧ Disjoint S T ∧ S≠T ∧
        hDisplacementLevel A w=S∪T := by
  by_cases hw : 0<(hHyperbolicAxis A hA ht).pointDist w
  · exact Or.inr (hDisplacementLevel_hyperbolic_two_branches A hA ht w hw)
  · left
    let L:=hHyperbolicAxis A hA ht
    have hw0 : L.pointDist w=0:=le_antisymm (not_lt.mp hw) (L.pointDist_nonneg w)
    obtain ⟨u,v,hu,_hv,_hne⟩:=L.exists_two_points
    apply hDisplacementLevel_hyperbolic_axis A hA ht w
    exact (L.isClosed_carrier.mem_iff_infDist_zero ⟨u,hu⟩).mpr hw0

/-- The original nontrivial conformal isometry has exactly the genuine complementary-curve levels
of its actual pencil; degenerate minima and the two-component hyperbolic levels are explicit. -/
theorem hDisplacementLevel_geometric_classification
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1) (w : ℍ) :
    (∃hE : Mobius.MobiusElliptic (realSLMobius A),
      let v:=hEllipticCenter A ((realSLMobius_elliptic_iff A hE.1).mp hE)
      hDisplacementLevel A w={v} ∨ hDisplacementLevel A w∈hMetricCircleFamily v) ∨
    (∃_hP : Mobius.MobiusParabolic (realSLMobius A),∃v : Mobius.ExtendedComplex,
      (realSLMobius A).val v=v ∧ IsHHorocycleAt v (hDisplacementLevel A w)) ∨
    (∃ht : 4<(Matrix.trace A.val)^2,
      hDisplacementLevel A w=(hHyperbolicAxis A hA ht).carrier ∨
      ∃S T : Set ℍ,IsHHypercycleBranch (hHyperbolicAxis A hA ht) S ∧
        IsHHypercycleBranch (hHyperbolicAxis A hA ht) T ∧ Disjoint S T ∧ S≠T ∧
        hDisplacementLevel A w=S∪T) := by
  rcases lt_trichotomy ((Matrix.trace A.val)^2) 4 with ht | ht | ht
  · let hE:Mobius.MobiusElliptic (realSLMobius A):=(realSLMobius_elliptic_iff A hA).mpr ht
    refine Or.inl ⟨hE,?_⟩
    rcases hDisplacementLevel_elliptic_regular_or_center A hE w with ⟨_hw,he⟩ | ⟨_hw,he⟩
    · exact Or.inl he
    · exact Or.inr he
  · let hP:Mobius.MobiusParabolic (realSLMobius A):=(realSLMobius_parabolic_iff A hA).mpr ht
    obtain ⟨v,hv,hlevel⟩:=hDisplacementLevel_parabolic A hP
    exact Or.inr (Or.inl ⟨hP,v,hv,hlevel w⟩)
  · exact Or.inr (Or.inr ⟨ht,hDisplacementLevel_hyperbolic_axis_or_two_branches A hA ht w⟩)

/-- Every regular elliptic displacement level is a genuine circle orthogonal to every actual associated pencil line. -/
theorem hDisplacementLevel_elliptic_orthogonal
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : Mobius.MobiusElliptic (realSLMobius A))
    (w : ℍ) (hw : w≠hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA))
    (L : HalfPlaneLine)
    (hL : L∈hEllipticPencil (hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA))) :
    ∃C : Mobius.ComplexGeneralizedCircle,hDisplacementLevel A w=halfPlaneCircleCarrier C ∧
      Mobius.ComplexCirclesOrthogonal L.extendedCircle C := by
  rw [hDisplacementLevel_elliptic A hA w]
  exact hMetricCircle_orthogonal _ _ (dist_pos.mpr hw) L hL

/-- Every full parabolic displacement level is a genuine circle orthogonal to every actual associated pencil line. -/
theorem hDisplacementLevel_parabolic_orthogonal
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : Mobius.MobiusParabolic (realSLMobius A)) :
    ∃v : Mobius.ExtendedComplex,(realSLMobius A).val v=v ∧
      ∀w : ℍ,∀L∈hParabolicPencil v,∃C : Mobius.ComplexGeneralizedCircle,
        hDisplacementLevel A w=halfPlaneCircleCarrier C ∧ Mobius.ComplexCirclesOrthogonal L.extendedCircle C := by
  obtain ⟨v,hv,hlevel⟩:=hDisplacementLevel_parabolic A hA
  refine ⟨v,hv,?_⟩
  intro w L hL
  exact hHorocycleAt_orthogonal (realSLMobius_parabolic_fixed_boundary A hA v hv) hL (hlevel w)

/-- Each genuine individual hyperbolic level branch is orthogonal to every actual associated pencil line. -/
theorem hHypercycleBranch_displacement_orthogonal
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1)
    (ht : 4<(Matrix.trace A.val)^2) {S : Set ℍ}
    (hS : IsHHypercycleBranch (hHyperbolicAxis A hA ht) S)
    (L : HalfPlaneLine) (hL : L∈hHyperbolicPencil (hHyperbolicAxis A hA ht)) :
    ∃C : Mobius.ComplexGeneralizedCircle,S=halfPlaneCircleCarrier C ∧
      Mobius.ComplexCirclesOrthogonal L.extendedCircle C := by
  exact hHypercycleBranch_orthogonal _ hL hS

end LowDimensionalTopology.Geometry.Hyperbolic
