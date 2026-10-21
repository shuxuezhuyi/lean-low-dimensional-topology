module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleSideNormals
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.TransversalAngles
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.LineCrossRatios
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
noncomputable section

/-- The existing geometric inversive product is invariant under the actual complex Möbius action. -/
theorem complexCircle_inversiveProduct_image (S T : Mobius.ComplexGeneralizedCircle) (f : Mobius.complexMobiusGroup) :
    Inversive.inversiveProduct (S.image f).realModel (T.image f).realModel =
      Inversive.inversiveProduct S.realModel T.realModel := by
  obtain ⟨g,hg,he⟩ := f.property.1
  have hreal (U : Mobius.ComplexGeneralizedCircle) :
      (U.image f).realModel = Inversive.generalizedSphereImage g hg U.realModel := by
    apply Subtype.ext
    change Mobius.extendedComplexEuclideanHomeomorph '' (f.val '' U.val) =
      g '' (Mobius.extendedComplexEuclideanHomeomorph '' U.val)
    rw [← he]
    exact Mobius.complexChart_image_image g U.val
  rw [hreal,hreal]
  exact Inversive.generalMobius_preservesInversiveProduct g hg S.realModel T.realModel

/-- Three distinct actual points uniquely determine their genuine generalized circle. -/
theorem complexCircles_eq_of_three_shared (S T : Mobius.ComplexGeneralizedCircle) (a b c : Mobius.ExtendedComplex)
    (hd : Mobius.TripleDistinct a b c) (haS : a ∈ S.val) (hbS : b ∈ S.val) (hcS : c ∈ S.val)
    (haT : a ∈ T.val) (hbT : b ∈ T.val) (hcT : c ∈ T.val) : S = T := by
  obtain ⟨q,h0,h1,hi⟩ := Mobius.mobius_normalize_triple a b c hd
  have hS := Mobius.complexCircle_through_zero_one_infty (S.property.image q.property.1)
    ⟨a,haS,h0⟩ ⟨b,hbS,h1⟩ ⟨c,hcS,hi⟩
  have hT := Mobius.complexCircle_through_zero_one_infty (T.property.image q.property.1)
    ⟨a,haT,h0⟩ ⟨b,hbT,h1⟩ ⟨c,hcT,hi⟩
  apply Subtype.ext
  exact q.val.injective.image_injective (hS.trans hT.symm)

/-- The real geometric inversive product equals the absolute normalized Lorentz side pairing. -/
theorem halfPlane_inversiveProduct_eq_normal_product (L M : HalfPlaneLine) :
    Inversive.inversiveProduct L.extendedCircle.realModel M.extendedCircle.realModel =
      |inner ℝ L.incenterNormal M.incenterNormal - L.incenterOffset * M.incenterOffset| := by
  cases L with
  | vertical a =>
    cases M with
    | vertical b =>
      rw [HalfPlaneLine.extendedCircle,HalfPlaneLine.extendedCircle,
        complexLine_realModel 1 a one_ne_zero,complexLine_realModel 1 b one_ne_zero,
        Inversive.inversiveProduct_plane_plane]
      simp only [Mobius.complexPlaneCoordinates.inner_map_map,Mobius.complexPlaneCoordinates.norm_map,
        real_inner_self_eq_norm_sq,norm_one,one_pow,abs_one,mul_one,div_one,
        HalfPlaneLine.incenterNormal, HalfPlaneLine.incenterOffset,
          _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
      ring_nf
      norm_num
    | circle c r hr =>
      rw [HalfPlaneLine.extendedCircle,HalfPlaneLine.extendedCircle,
        complexLine_realModel 1 a one_ne_zero,complexCircle_realModel c r hr,Inversive.inversiveProduct_comm,
        Inversive.inversiveProduct_sphere_plane]
      simp only [Mobius.complexPlaneCoordinates.inner_map_map,Mobius.complexPlaneCoordinates.norm_map,norm_one,mul_one,
        _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im,
        mul_one,mul_zero,add_zero,HalfPlaneLine.incenterNormal,HalfPlaneLine.incenterOffset]
      calc
        _ = |(a - c) / r| := by rw [abs_div,abs_of_pos hr,abs_sub_comm]
        _ = _ := by congr 1; field_simp; ring
  | circle c r hr =>
    cases M with
    | vertical a =>
      rw [HalfPlaneLine.extendedCircle,HalfPlaneLine.extendedCircle,
        complexCircle_realModel c r hr,complexLine_realModel 1 a one_ne_zero,Inversive.inversiveProduct_sphere_plane]
      simp only [Mobius.complexPlaneCoordinates.inner_map_map,Mobius.complexPlaneCoordinates.norm_map,norm_one,mul_one,
        _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im,
        mul_one,mul_zero,add_zero,HalfPlaneLine.incenterNormal,HalfPlaneLine.incenterOffset]
      calc
        _ = |(a - c) / r| := by rw [abs_div,abs_of_pos hr,abs_sub_comm]
        _ = _ := by congr 1; field_simp; ring
    | circle d s hs =>
      rw [HalfPlaneLine.extendedCircle,HalfPlaneLine.extendedCircle,
        complexCircle_realModel c r hr,complexCircle_realModel d s hs,Inversive.inversiveProduct_sphere_sphere]
      rw [← map_sub,Mobius.complexPlaneCoordinates.norm_map,←
        Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      simp only [HalfPlaneLine.incenterNormal, HalfPlaneLine.incenterOffset,
        _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
      congr 1
      field_simp
      ring


def geodesicRealGLMobius (g : GL (Fin 2) ℝ) : Mobius.complexMobiusGroup :=
  ⟨Mobius.fractionalLinear (complexifiedRealMobiusMatrix g),by
    rw [Mobius.complexMobiusGroup_eq_fractionalLinearGroup]
    exact ⟨complexifiedRealMobiusMatrix g,rfl⟩⟩

/-- Equality of actual H carriers determines the entire real geometric generalized circle image. -/
theorem HalfPlaneLine.extendedCircle_image_realGL (L M : HalfPlaneLine) (g : GL (Fin 2) ℝ)
    (hg : 0 < g.val.det) (hL : (g • · : ℍ → ℍ) '' L.carrier = M.carrier) :
    L.extendedCircle.image (geodesicRealGLMobius g) = M.extendedCircle := by
  obtain ⟨γ,hγ,hrange⟩ := L.exists_isometric_param
  let ζ : ℝ → Mobius.ExtendedComplex := fun t => (((g • γ t : ℍ) : ℂ) : Mobius.ExtendedComplex)
  have hζ : Function.Injective ζ := by
    intro t u he
    apply hγ.injective
    apply (realGL_isometry g).injective
    apply UpperHalfPlane.ext
    exact OnePoint.coe_injective he
  have hS (t : ℝ) : ζ t ∈ (L.extendedCircle.image (geodesicRealGLMobius g)).val := by
    refine ⟨(((γ t : ℍ) : ℂ) : Mobius.ExtendedComplex),?_,?_⟩
    · exact (L.mem_extendedCircle (γ t)).mpr (hrange ▸ mem_range_self t)
    · exact realMobiusMatrix_coe g hg (γ t)
  have hM (t : ℝ) : ζ t ∈ M.extendedCircle.val := by
    apply (M.mem_extendedCircle (g • γ t)).mpr
    rw [← hL]
    exact mem_image_of_mem (g • ·) (hrange ▸ mem_range_self t)
  exact complexCircles_eq_of_three_shared _ _ (ζ 0) (ζ 1) (ζ 2)
    ⟨hζ.ne (by norm_num),hζ.ne (by norm_num),hζ.ne (by norm_num)⟩
    (hS 0) (hS 1) (hS 2) (hM 0) (hM 1) (hM 2)

theorem halfPlane_inversiveProduct_realGL_image (L M L' M' : HalfPlaneLine)
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hL : (g • · : ℍ → ℍ) '' L.carrier = L'.carrier)
    (hM : (g • · : ℍ → ℍ) '' M.carrier = M'.carrier) :
    Inversive.inversiveProduct L'.extendedCircle.realModel M'.extendedCircle.realModel =
      Inversive.inversiveProduct L.extendedCircle.realModel M.extendedCircle.realModel := by
  rw [← L.extendedCircle_image_realGL L' g hg hL,← M.extendedCircle_image_realGL M' g hg hM]
  exact complexCircle_inversiveProduct_image L.extendedCircle M.extendedCircle (geodesicRealGLMobius g)

theorem disc_inversiveProduct_eq_halfPlane (L M : DiscLine) :
    Inversive.inversiveProduct L.val.realModel M.val.realModel =
      Inversive.inversiveProduct L.toHalfPlane.extendedCircle.realModel M.toHalfPlane.extendedCircle.realModel := by
  have he := complexCircle_inversiveProduct_image L.toHalfPlane.extendedCircle M.toHalfPlane.extendedCircle cayleyMobius
  change Inversive.inversiveProduct L.toHalfPlane.toDiscLine.val.realModel M.toHalfPlane.toDiscLine.val.realModel =
    _ at he
  simpa only [L.toHalfPlane_spec,M.toHalfPlane_spec] using he


theorem halfPlane_inversiveProduct_eq_cos_acuteAngle (L M : HalfPlaneLine) (p : ℍ)
    (hpL : p ∈ L.carrier) (hpM : p ∈ M.carrier) :
    Inversive.inversiveProduct L.extendedCircle.realModel M.extendedCircle.realModel = Real.cos (L.acuteAngle M p) := by
  have hangle : L.acuteAngle M p =
      acuteTangentAngle (Complex.I * L.incenterNormalAt p) (Complex.I * M.incenterNormalAt p) := by
    unfold HalfPlaneLine.acuteAngle
    conv_lhs => rw [L.tangentAt_eq_incenterNormalAt p hpL,M.tangentAt_eq_incenterNormalAt p hpM]
    rw [acuteTangentAngle_smul_left _ _ _ (norm_ne_zero_iff.mpr (L.tangentAt_ne_zero p)),
      acuteTangentAngle_smul_right _ _ _ (norm_ne_zero_iff.mpr (M.tangentAt_ne_zero p))]
  rw [halfPlane_inversiveProduct_eq_normal_product,hangle,acuteTangentAngle_cos,
    complex_inner_rotate,L.incenterNormalAt_inner M p hpL hpM]
  simp only [norm_mul,Complex.norm_I,L.incenterNormalAt_norm p hpL,M.incenterNormalAt_norm p hpM,
    mul_one,div_one]

theorem disc_inversiveProduct_eq_cos_acuteAngle (L M : DiscLine) (p : 𝔻)
    (hpL : p ∈ L.carrier) (hpM : p ∈ M.carrier) :
    Inversive.inversiveProduct L.val.realModel M.val.realModel = Real.cos (L.acuteAngle M p hpL hpM) := by
  rw [disc_inversiveProduct_eq_halfPlane,L.acuteAngle_eq_halfPlane M p hpL hpM]
  exact halfPlane_inversiveProduct_eq_cos_acuteAngle L.toHalfPlane M.toHalfPlane (discToHalfPlane p)
    ((L.mem_carrier p).mp hpL) ((M.mem_carrier p).mp hpM)

theorem halfPlane_inversiveProduct_eq_one_of_parallel (L M : HalfPlaneLine) (hp : L.Parallel M) :
    Inversive.inversiveProduct L.extendedCircle.realModel M.extendedCircle.realModel = 1 := by
  obtain ⟨g,a,b,hg,_,hL,hM⟩ := L.exists_parallel_vertical_normalizer M hp
  rw [← halfPlane_inversiveProduct_realGL_image L M (.vertical a) (.vertical b) g hg hL hM,
    halfPlane_inversiveProduct_eq_normal_product]
  simp only [HalfPlaneLine.incenterNormal, HalfPlaneLine.incenterOffset,
    _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
  have he : a * b + (-1 : ℝ) * (-1) - a * b = 1 := by ring
  rw [he,abs_one]

theorem cosh_abs_log_ratio (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    Real.cosh |Real.log (s / t)| = (s ^ 2 + t ^ 2) / (2 * s * t) := by
  have habs (x : ℝ) : Real.cosh |x| = Real.cosh x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx),Real.cosh_neg]
  rw [habs,Real.cosh_log (div_pos hs ht)]
  field_simp

theorem concentric_inversiveProduct_eq_cosh_lineDist (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    Inversive.inversiveProduct (HalfPlaneLine.circle 0 s hs).extendedCircle.realModel
      (HalfPlaneLine.circle 0 t ht).extendedCircle.realModel =
      Real.cosh ((HalfPlaneLine.circle 0 s hs).lineDist (.circle 0 t ht)) := by
  rw [HalfPlaneLine.extendedCircle,HalfPlaneLine.extendedCircle,
    complexCircle_realModel ((0 : ℝ) : ℂ) s hs,complexCircle_realModel ((0 : ℝ) :
      ℂ) t ht,Inversive.inversiveProduct_sphere_sphere,
    sub_self,norm_zero,zero_pow (by norm_num : 2 ≠ 0),sub_zero,concentric_lineDist,
    cosh_abs_log_ratio s t hs ht]
  rw [abs_of_pos (by positivity : 0 < (s ^ 2 + t ^ 2) / (2 * s * t))]

theorem halfPlane_inversiveProduct_eq_cosh_lineDist (L M : HalfPlaneLine) (hd : L.HDisjoint M) :
    Inversive.inversiveProduct L.extendedCircle.realModel M.extendedCircle.realModel = Real.cosh (L.lineDist M) := by
  obtain ⟨g,s,t,hs,ht,hg,_,hL,hM⟩ := L.exists_concentric_normalizer M hd
  rw [← halfPlane_inversiveProduct_realGL_image L M (.circle 0 s hs) (.circle 0 t ht) g hg hL hM,
    concentric_inversiveProduct_eq_cosh_lineDist s t hs ht,
    L.lineDist_isometry_image M (.circle 0 s hs) (.circle 0 t ht) (g • ·) (realGL_isometry g) hL hM]


theorem disc_inversiveProduct_eq_one_of_parallel (L M : DiscLine) (hp : L.Parallel M) :
    Inversive.inversiveProduct L.val.realModel M.val.realModel = 1 := by
  rw [disc_inversiveProduct_eq_halfPlane]
  exact halfPlane_inversiveProduct_eq_one_of_parallel L.toHalfPlane M.toHalfPlane
    (L.parallel_toHalfPlane M hp)

theorem disc_inversiveProduct_eq_cosh_lineDist (L M : DiscLine) (hd : L.HDisjoint M) :
    Inversive.inversiveProduct L.val.realModel M.val.realModel = Real.cosh (L.lineDist M) := by
  rw [disc_inversiveProduct_eq_halfPlane,L.lineDist_eq_halfPlane M]
  exact halfPlane_inversiveProduct_eq_cosh_lineDist L.toHalfPlane M.toHalfPlane
    ((L.hDisjoint_iff_halfPlane M).mp hd)

/-- In the actual H model, using genuine pair-distance infima and tangent angles. -/
theorem HalfPlaneLine.inversiveProduct_distance_parallel_angle_cases (L M : HalfPlaneLine) :
    (L.HDisjoint M → Inversive.inversiveProduct L.extendedCircle.realModel M.extendedCircle.realModel =
      Real.cosh (L.lineDist M)) ∧
    (L.Parallel M → Inversive.inversiveProduct L.extendedCircle.realModel M.extendedCircle.realModel = 1) ∧
    (∀ p ∈ L.carrier, p ∈ M.carrier →
      Inversive.inversiveProduct L.extendedCircle.realModel M.extendedCircle.realModel = Real.cos (L.acuteAngle M p)) :=
  ⟨halfPlane_inversiveProduct_eq_cosh_lineDist L M,halfPlane_inversiveProduct_eq_one_of_parallel L M,
    halfPlane_inversiveProduct_eq_cos_acuteAngle L M⟩

/-- The same three source branches for native D circles and diameters, without surrogate metrics. -/
theorem DiscLine.inversiveProduct_distance_parallel_angle_cases (L M : DiscLine) :
    (L.HDisjoint M → Inversive.inversiveProduct L.val.realModel M.val.realModel = Real.cosh (L.lineDist M)) ∧
    (L.Parallel M → Inversive.inversiveProduct L.val.realModel M.val.realModel = 1) ∧
    (∀ (p : 𝔻) (hpL : p ∈ L.carrier) (hpM : p ∈ M.carrier),
      Inversive.inversiveProduct L.val.realModel M.val.realModel = Real.cos (L.acuteAngle M p hpL hpM)) :=
  ⟨disc_inversiveProduct_eq_cosh_lineDist L M,disc_inversiveProduct_eq_one_of_parallel L M,
    disc_inversiveProduct_eq_cos_acuteAngle L M⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
