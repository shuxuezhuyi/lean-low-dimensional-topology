/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicAxes
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfSpace.HorosphereParametrization
@[expose] public section
noncomputable section
open Set
open scoped OnePoint UpperHalfPlane MatrixGroups ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual real vertical Poincare plane is parametrized by the actual upper half-plane. -/
def halfPlaneH3Embed (z : ℍ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint (z.re:ℂ) z.im z.im_pos

theorem halfPlaneH3Embed_injective : Function.Injective halfPlaneH3Embed := by
  intro z w he
  apply UpperHalfPlane.ext
  apply Complex.ext
  · have h := congrArg (fun p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionHorizontal p.val).re) he
    exact h
  · exact congrArg (fun p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionHeight p.val) he

theorem halfPlaneH3Embed_continuous : Continuous halfPlaneH3Embed := by
  apply Continuous.subtype_mk
  change Continuous (fun z : ℍ =>
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionThreePointCLM ((z.re:ℂ),z.im))
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionThreePointCLM.continuous.comp
  exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_re).prodMk UpperHalfPlane.continuous_im

/-- The real-matrix denominator is the actual native complex fractional denominator. -/
theorem halfPlaneH3_denominator (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    Mobius.poincareDenominator (A.val.map Complex.ofRealHom) (z.re:ℂ) z.im=
      Complex.normSq ((A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ)) := by
  simp only [Mobius.poincareDenominator,Matrix.map_apply,Complex.ofRealHom_eq_coe,
    Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,mul_zero,zero_mul,add_zero,sub_zero]
  ring

/-- The actual Poincare horizontal coordinate is exactly the native real Mobius coordinate. -/
theorem halfPlaneH3_horizontal (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    Mobius.poincareHorizontal (A.val.map Complex.ofRealHom) (z.re:ℂ) z.im=((A•z).re:ℂ) := by
  have hfrac := UpperHalfPlane.coe_specialLinearGroup_apply A z
  have hre := congrArg Complex.re hfrac
  change (A•z).re=(((A 0 0:ℂ)*(z:ℂ)+(A 0 1:ℂ))/((A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ))).re at hre
  rw [hre]
  have hnum :
      ((A 0 0:ℂ)*(z.re:ℂ)+(A 0 1:ℂ))*conj ((A 1 0:ℂ)*(z.re:ℂ)+(A 1 1:ℂ))+
        (A 0 0:ℂ)*conj (A 1 0:ℂ)*(z.im:ℂ)^2=
      (((A 0 0*z.re+A 0 1)*(A 1 0*z.re+A 1 1)+A 0 0*A 1 0*z.im^2:ℝ):ℂ) := by
    push_cast
    simp only [map_add,map_mul,Complex.conj_ofReal]
  simp only [Mobius.poincareHorizontal,Matrix.map_apply,Complex.ofRealHom_eq_coe]
  rw [hnum,←Complex.ofReal_div]
  apply congrArg Complex.ofReal
  rw [halfPlaneH3_denominator,Complex.div_re]
  simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,
    zero_mul,add_zero,sub_zero]
  ring


/-- The actual Poincare height is exactly the native half-plane imaginary coordinate. -/
theorem halfPlaneH3_height (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    Mobius.poincareHeight (A.val.map Complex.ofRealHom) (z.re:ℂ) z.im=(A•z).im := by
  have hd : (A.val.map Complex.ofRealHom).det=1 :=
    (Matrix.SpecialLinearGroup.map Complex.ofRealHom A).property
  rw [Mobius.poincareHeight,hd,norm_one,one_mul,halfPlaneH3_denominator]
  symm
  change ((Matrix.SpecialLinearGroup.mapGL ℝ A)•z).im=_
  rw [UpperHalfPlane.im_smul_eq_div_normSq]
  simp only [Matrix.SpecialLinearGroup.det_mapGL,Units.val_one,abs_one,one_mul]
  rfl

/-- The native half-plane embedding is equivariant for the entire genuine Poincare action. -/
theorem halfPlaneH3Embed_realSL (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    realSLMobius A • halfPlaneH3Embed z=halfPlaneH3Embed (A•z) := by
  change Mobius.mobiusSpecialLinearProjection (Matrix.SpecialLinearGroup.map Complex.ofRealHom A) •
    halfPlaneH3Embed z=halfPlaneH3Embed (A•z)
  rw [Mobius.mobiusUpperHalfSpace_smul,Mobius.mobiusPoincareHom_specialLinearProjection]
  apply Subtype.ext
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionThreePoint
      (Mobius.poincareHorizontal (A.val.map Complex.ofRealHom) (z.re:ℂ) z.im)
      (Mobius.poincareHeight (A.val.map Complex.ofRealHom) (z.re:ℂ) z.im)=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionThreePoint ((A•z).re:ℂ) (A•z).im
  rw [halfPlaneH3_horizontal,halfPlaneH3_height]


/-- The entire native imaginary axis is exactly the actual vertical geodesic in H3. -/
theorem halfPlaneH3Embed_vertical_image :
    halfPlaneH3Embed '' {z : ℍ | z.re=0}=DiscreteGroups.mobiusVerticalGeodesic := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change (z.re:ℂ)=0
    rw [hz,Complex.ofReal_zero]
  · intro hx
    let z := metricProbe 0 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionHeight
      x.val) x.property
    refine ⟨z,rfl,?_⟩
    apply Subtype.ext
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates x.val]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (0:ℂ) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val)
    rw [show _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val=0 from hx]

/-- Entire geometric subsets are transported by the actual equivariant embedding. -/
theorem halfPlaneH3Embed_image_realSL (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (S : Set ℍ) :
    (fun p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => realSLMobius
      A•p) '' (halfPlaneH3Embed '' S)=
      halfPlaneH3Embed '' ((fun z : ℍ => A•z) '' S) := by
  rw [image_image,image_image]
  congr 1
  funext z
  exact halfPlaneH3Embed_realSL A z

/-- The native complete hyperbolic axis is carried to the whole native imaginary axis. -/
theorem hHyperbolicAxis_native_image (f q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) (ht : 4<(Matrix.trace f.val)^2)
    (hc : (hHyperbolicAxis f hf ht).carrier={z : ℍ | (q•z).re=0}) :
    (fun z : ℍ => q•z) '' (hHyperbolicAxis f hf ht).carrier={z : ℍ | z.re=0} := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    rw [hc] at hw
    exact hw
  · intro hz
    refine ⟨q⁻¹•z,?_,smul_inv_smul q z⟩
    rw [hc]
    change (q•(q⁻¹•z)).re=0
    rwa [smul_inv_smul]

/-- The actual native H2 axis and the genuine Poincare H3 geodesic axis are the same
entire geometric line under the proved equivariant embedding. -/
theorem halfPlaneH3Embed_hyperbolic_axis (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) (ht : 4<(Matrix.trace f.val)^2) :
    DiscreteGroups.mobiusGeodesicAxis (realSLMobius f)=halfPlaneH3Embed '' (hHyperbolicAxis f hf ht).carrier := by
  obtain ⟨q,k,hk,hk1,hn,_⟩ := realSLMobius_hyperbolic_normalizer f hf ht
  have hc := hHyperbolicAxis_normalizer_carrier f hf ht q k hk hk1 hn
  have hu : ((Units.mk0 (k:ℂ) (Complex.ofReal_ne_zero.mpr hk.ne'):ℂˣ):ℂ)≠1 := by
    intro he
    exact hk1 (Complex.ofReal_injective he)
  have hleft : (fun p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
    realSLMobius q•p) '' DiscreteGroups.mobiusGeodesicAxis (realSLMobius f)=
      DiscreteGroups.mobiusVerticalGeodesic := by
    rw [←DiscreteGroups.mobiusGeodesicAxis_conjugation,←map_inv,←map_mul,←map_mul,hn,
      DiscreteGroups.mobiusScaling_eq_standard _ hu,DiscreteGroups.mobiusGeodesicAxis_standard _ hu]
  have hright : (fun p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
    realSLMobius q•p) ''
      (halfPlaneH3Embed '' (hHyperbolicAxis f hf ht).carrier)=DiscreteGroups.mobiusVerticalGeodesic := by
    rw [halfPlaneH3Embed_image_realSL,hHyperbolicAxis_native_image f q hf ht hc,
      halfPlaneH3Embed_vertical_image]
  exact (Set.image_injective.mpr (MulAction.injective (realSLMobius q))) (hleft.trans hright.symm)


/-- The actual finite-chart embedding of the native half-plane is injective. -/
theorem halfPlaneSpherePoint_injective : Function.Injective extendedHalfPlanePoint := by
  intro z w h
  exact UpperHalfPlane.ext (OnePoint.coe_injective h)

/-- The whole native sphere image is equivariant for the same actual real Mobius map. -/
theorem halfPlaneSpherePoint_image_realSL (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (S : Set ℍ) :
    (realSLMobius A).val '' (extendedHalfPlanePoint '' S)=
      extendedHalfPlanePoint '' ((fun z : ℍ => A•z) '' S) := by
  rw [image_image,image_image]
  congr 1
  funext z
  exact realSLMobius_action A z

/-- Equality of entire translated axes agrees in the actual H3 and original sphere models. -/
theorem hyperbolic_axis_translate_eq_iff (A f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) (ht : 4<(Matrix.trace f.val)^2) :
    (fun p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => realSLMobius
      A•p) '' DiscreteGroups.mobiusGeodesicAxis (realSLMobius f)=
        DiscreteGroups.mobiusGeodesicAxis (realSLMobius f) ↔
      (realSLMobius A).val '' (extendedHalfPlanePoint '' (hHyperbolicAxis f hf ht).carrier)=
        extendedHalfPlanePoint '' (hHyperbolicAxis f hf ht).carrier := by
  rw [halfPlaneH3Embed_hyperbolic_axis f hf ht,halfPlaneH3Embed_image_realSL,halfPlaneSpherePoint_image_realSL]
  exact halfPlaneH3Embed_injective.image_injective.eq_iff.trans
    halfPlaneSpherePoint_injective.image_injective.eq_iff.symm

/-- Genuine disjointness of entire axes agrees in the two actual geometric models. -/
theorem hyperbolic_axis_translate_disjoint_iff (A f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) (ht : 4<(Matrix.trace f.val)^2) :
    Disjoint ((fun p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
      realSLMobius A•p) '' DiscreteGroups.mobiusGeodesicAxis (realSLMobius f))
        (DiscreteGroups.mobiusGeodesicAxis (realSLMobius f)) ↔
      Disjoint ((realSLMobius A).val '' (extendedHalfPlanePoint '' (hHyperbolicAxis f hf ht).carrier))
        (extendedHalfPlanePoint '' (hHyperbolicAxis f hf ht).carrier) := by
  rw [halfPlaneH3Embed_hyperbolic_axis f hf ht,halfPlaneH3Embed_image_realSL,halfPlaneSpherePoint_image_realSL]
  rw [Set.disjoint_image_iff halfPlaneH3Embed_injective,
    Set.disjoint_image_iff halfPlaneSpherePoint_injective]

/-- Simplicity is exactly original sphere-axis stability, with every actual group
transformation lifted by the proved whole-group normalization. -/
theorem isSimple_iff_native_axis_stable (H : Subgroup Mobius.complexMobiusGroup)
    (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hf : realSLMobius f≠1)
    (ht : 4<(Matrix.trace f.val)^2)
    (hLift : ∀ g ∈ H, ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, realSLMobius A=g) :
    Fuchsian.IsSimple H (realSLMobius f) ↔ realSLMobius f ∈ H ∧
      _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSet H (extendedHalfPlanePoint '' (hHyperbolicAxis f hf ht).carrier) := by
  constructor
  · intro hs
    refine ⟨hs.1,?_⟩
    intro g hg
    obtain ⟨A,rfl⟩ := hLift g hg
    rcases hs.2.2 (realSLMobius A) hg with he | hd
    · exact Or.inl ((hyperbolic_axis_translate_eq_iff A f hf ht).mp he)
    · exact Or.inr ((hyperbolic_axis_translate_disjoint_iff A f hf ht).mp hd)
  · rintro ⟨hfH,hs⟩
    refine ⟨hfH,(realSLMobius_hyperbolic_iff f hf).mpr ht,?_⟩
    intro g hg
    obtain ⟨A,rfl⟩ := hLift g hg
    rcases hs (realSLMobius A) hg with he | hd
    · exact Or.inl ((hyperbolic_axis_translate_eq_iff A f hf ht).mpr he)
    · exact Or.inr ((hyperbolic_axis_translate_disjoint_iff A f hf ht).mpr hd)


/-- Actual subgroup conjugation cancels with its inverse on the entire subgroup. -/
theorem subgroupConjugate_inv_cancel (q : Mobius.complexMobiusGroup) (H : Subgroup Mobius.complexMobiusGroup) :
    DiscreteGroups.Action.Actions.subgroupConjugate q⁻¹ (DiscreteGroups.Action.Actions.subgroupConjugate q H)=H := by
  ext g
  constructor
  · intro hg
    obtain ⟨a,ha,he⟩ := (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q⁻¹ _ g).mp hg
    obtain ⟨b,hb,hba⟩ := (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H a).mp ha
    have hgb : g=b := by rw [←he,←hba]; group
    rwa [hgb]
  · intro hg
    apply (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q⁻¹ _ g).mpr
    exact ⟨q*g*q⁻¹,(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨g,hg,rfl⟩,by group⟩

/-- Simplicity is exactly invariant under the actual whole-group geometric conjugation. -/
theorem isSimple_conjugation (H : Subgroup Mobius.complexMobiusGroup) (f q : Mobius.complexMobiusGroup) :
    Fuchsian.IsSimple (DiscreteGroups.Action.Actions.subgroupConjugate q H) (q*f*q⁻¹) ↔ Fuchsian.IsSimple H f := by
  constructor
  · intro h
    have hh := h.conjugate q⁻¹
    rw [subgroupConjugate_inv_cancel] at hh
    have he : q⁻¹*(q*f*q⁻¹)*(q⁻¹)⁻¹=f := by group
    rwa [he] at hh
  · intro h
    exact h.conjugate q

/-- Every original Fuchsian disc has an equivalent genuine stable native-axis description;
the actual matrix, its hyperbolicity and its entire axis are constructed conclusions. -/
theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.isSimple_iff_exists_native_axis_stable {H :
  Subgroup Mobius.complexMobiusGroup}
    (D : Fuchsian.FuchsianDisc H) (f : Mobius.complexMobiusGroup) (hfH : f ∈ H) :
    Fuchsian.IsSimple H f ↔ ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∃ hA : realSLMobius A≠1, ∃ htrace : 4<(Matrix.trace A.val)^2,
        realSLMobius A=D.halfPlaneNormalizer*f*D.halfPlaneNormalizer⁻¹ ∧
        _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSet D.normalizedGroup
          (extendedHalfPlanePoint '' (hHyperbolicAxis A hA htrace).carrier) := by
  let q := D.halfPlaneNormalizer
  have hfK : q*f*q⁻¹ ∈ D.normalizedGroup :=
    (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨f,hfH,rfl⟩
  constructor
  · intro hs
    obtain ⟨A,hAe⟩ := D.normalizedGroup_exists_realSL (q*f*q⁻¹) hfK
    have hAs : Fuchsian.IsSimple D.normalizedGroup (realSLMobius A) := by
      rw [hAe]
      exact hs.conjugate q
    have hA : realSLMobius A≠1 := hAs.2.1.1.1
    have ht : 4<(Matrix.trace A.val)^2 := (realSLMobius_hyperbolic_iff A hA).mp hAs.2.1
    exact ⟨A,hA,ht,hAe,((isSimple_iff_native_axis_stable D.normalizedGroup A hA ht
      D.normalizedGroup_exists_realSL).mp hAs).2⟩
  · rintro ⟨A,hA,ht,hAe,hstable⟩
    have hAmem : realSLMobius A ∈ D.normalizedGroup := hAe.symm ▸ hfK
    have hAs := (isSimple_iff_native_axis_stable D.normalizedGroup A hA ht
      D.normalizedGroup_exists_realSL).mpr ⟨hAmem,hstable⟩
    rw [hAe] at hAs
    exact (isSimple_conjugation H f q).mp hAs

end LowDimensionalTopology.Geometry.Hyperbolic
