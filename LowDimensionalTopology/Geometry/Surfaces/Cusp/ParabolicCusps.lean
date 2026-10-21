module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Surfaces.Quotient.StableSets
public import LowDimensionalTopology.Geometry.Mobius.InvariantDisc.InvariantDiscConverse
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenInequality
public import LowDimensionalTopology.Geometry.Mobius.Topology.MobiusOmittedValues
public import Mathlib.Analysis.Complex.Convex
@[expose] public section
noncomputable section
open Set Filter Topology TopologicalSpace
open scoped OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The literal normalized horodisc in finite complex coordinates. -/
def stableCuspHalfPlane (h : ℝ) : Set ℂ := {z | h < z.im}

/-- Its punctured-disc radius in the actual period-one exponential coordinate. -/
def stableCuspRadius (h : ℝ) : ℝ := Real.exp (-2 * Real.pi * h)

theorem stableCuspRadius_pos (h : ℝ) : 0 < stableCuspRadius h := Real.exp_pos _

/-- The actual exponential coordinate has exactly the stated hyperbolic-cusp modulus. -/
theorem stableCuspExponential_norm (z : ℂ) :
    ‖(complexPeriodExponential 1 z).val‖ = Real.exp (-2 * Real.pi * z.im) := by
  change ‖Complex.exp ((2 * Real.pi * Complex.I / 1) * z)‖ = _
  rw [Complex.norm_exp]
  congr 1
  norm_num [Complex.mul_re, Complex.mul_im]

/-- The finite cusp is precisely the preimage of the genuine punctured radius ball. -/
theorem stableCuspExponential_mem (h : ℝ) (z : ℂ) :
    ‖(complexPeriodExponential 1 z).val‖ < stableCuspRadius h ↔ z ∈ stableCuspHalfPlane h := by
  rw [stableCuspExponential_norm, stableCuspRadius, Real.exp_lt_exp]
  change -2 * Real.pi * z.im < -2 * Real.pi * h ↔ h < z.im
  constructor <;> intro hz <;> nlinarith [Real.pi_pos]

/-- The literal punctured disc, as an open subspace of the actual punctured complex plane. -/
def stableCuspPuncturedDisc (h : ℝ) : Set {z : ℂ // z ≠ 0} :=
  {z | ‖z.val‖ < stableCuspRadius h}

theorem stableCuspPuncturedDisc_isOpen (h : ℝ) : IsOpen (stableCuspPuncturedDisc h) :=
  isOpen_lt (continuous_subtype_val.norm) continuous_const

/-- The actual exponential restricted to the literal normalized cusp. -/
def stableCuspExponential (h : ℝ) : stableCuspHalfPlane h → stableCuspPuncturedDisc h :=
  fun z => ⟨complexPeriodExponential 1 z.val, (stableCuspExponential_mem h z.val).mpr z.property⟩

theorem stableCuspExponential_continuous (h : ℝ) : Continuous (stableCuspExponential h) :=
  ((complexPeriodExponential 1).continuous.comp continuous_subtype_val).subtype_mk _

/-- Every point of the actual punctured disc has an original cusp representative. -/
theorem stableCuspExponential_surjective (h : ℝ) : Function.Surjective (stableCuspExponential h) := by
  intro w
  obtain ⟨z, hz⟩ := (complexPeriodExponential_isQuotientMap 1 one_ne_zero).surjective w.val
  have hzm : z ∈ stableCuspHalfPlane h := (stableCuspExponential_mem h z).mp (by
    rw [hz]
    exact w.property)
  exact ⟨⟨z, hzm⟩, Subtype.ext hz⟩

/-- The exponential restriction is an actual open quotient map onto the punctured disc. -/
theorem stableCuspExponential_isOpenQuotientMap (h : ℝ) : IsOpenQuotientMap (stableCuspExponential h) := by
  have hconst : (2 * Real.pi * Complex.I / 1 : ℂ) ≠ 0 := by
    simp only [div_one]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have he : IsOpenMap (complexPeriodExponential 1) := by
    change IsOpenMap ((fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘
      Homeomorph.mulLeft₀ (2 * Real.pi * Complex.I / 1) hconst)
    exact Complex.isAddQuotientCoveringMap_exp.isCoveringMap.isOpenMap.comp
      (Homeomorph.mulLeft₀ _ hconst).isOpenMap
  have hH : IsOpen (stableCuspHalfPlane h) := isOpen_lt continuous_const Complex.continuous_im
  exact ⟨stableCuspExponential_surjective h, stableCuspExponential_continuous h,
    (he.comp hH.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _⟩

/-- The literal normalized cusp is convex and nonempty in its finite chart. -/
theorem stableCuspHalfPlane_isConnected (h : ℝ) : IsConnected (stableCuspHalfPlane h) := by
  have hc : Convex ℝ (stableCuspHalfPlane h) := (convex_Ioi h).linear_preimage Complex.imLm
  exact hc.isConnected ⟨(⟨0, h + 1⟩ : ℂ), by change h < h + 1; linarith⟩

/-- The true sphere subset of the normalized horodisc, with the ordinary sphere topology. -/
def stableCuspSphere (h : ℝ) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' stableCuspHalfPlane h

theorem stableCuspSphere_isOpen (h : ℝ) : IsOpen (stableCuspSphere h) :=
  OnePoint.isOpenEmbedding_coe.isOpenMap _ (isOpen_lt continuous_const Complex.continuous_im)

theorem stableCuspSphere_isConnected (h : ℝ) : IsConnected (stableCuspSphere h) :=
  (stableCuspHalfPlane_isConnected h).image ((↑) : ℂ →
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) OnePoint.continuous_coe.continuousOn

/-- Actual integer translations preserve the entire literal normalized horodisc. -/
theorem stableCuspSphere_translation (h : ℝ) (n : ℤ) :
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (n : ℂ)).val '' stableCuspSphere h = stableCuspSphere h := by
  ext p
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
    exact ⟨z + n, by simpa only [stableCuspHalfPlane, mem_ofPred_eq, Complex.add_im,
      Complex.intCast_im, add_zero] using hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hm : z - n ∈ stableCuspHalfPlane h := by
      simpa only [stableCuspHalfPlane, mem_ofPred_eq, Complex.sub_im, Complex.intCast_im, sub_zero] using hz
    refine ⟨((z - n : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ⟨z - n, hm, rfl⟩, ?_⟩
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
    congr 1
    ring

/-- The original actual period-one parabolic group acting on its genuine horodisc. -/
def stableCuspDomain (h : ℝ) : MobiusInvariantDomain stableTranslationGroup where
  carrier := stableCuspSphere h
  isOpen := stableCuspSphere_isOpen h
  isConnected := stableCuspSphere_isConnected h
  invariant := by
    intro g z hz
    obtain ⟨n, hn⟩ := (stableTranslationGroup_mem g.val).mp g.property
    change g.val.val z ∈ stableCuspSphere h
    rw [hn]
    exact stableCuspSphere_translation h n ▸ ⟨z, hz, rfl⟩

/-- The finite cusp coordinate is a true homeomorphism to the actual sphere subdomain. -/
def stableCuspHalfPlaneHomeomorph (h : ℝ) : stableCuspHalfPlane h ≃ₜ (stableCuspDomain h).carrier :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage (stableCuspHalfPlane h)

@[simp] theorem stableCuspHalfPlaneHomeomorph_coe (h : ℝ) (z : stableCuspHalfPlane h) :
    (stableCuspHalfPlaneHomeomorph h z).val = (z.val :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := rfl

/-- Actual parabolic cusp orbits are exactly the fibers of the genuine punctured-disc
exponential coordinate. -/
theorem stableCuspDomain_orbitRel_iff (h : ℝ) (z w : stableCuspHalfPlane h) :
    MulAction.orbitRel stableTranslationGroup (stableCuspDomain h).carrier
      (stableCuspHalfPlaneHomeomorph h z) (stableCuspHalfPlaneHomeomorph h w) ↔
      stableCuspExponential h z = stableCuspExponential h w := by
  rw [Subtype.ext_iff]
  change _ ↔ complexPeriodExponential 1 z.val = complexPeriodExponential 1 w.val
  rw [complexPeriodExponential_fiber_iff 1 one_ne_zero]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨n, hn⟩ := (stableTranslationGroup_mem g.val).mp g.property
    have he : g.val.val (w.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (z.val :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := congrArg Subtype.val hg
    rw [hn, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe] at he
    have hzw : w.val + (n : ℂ) = z.val := OnePoint.coe_injective he
    refine ⟨n, ?_⟩
    change n • (1 : ℂ) = z.val - w.val
    rw [zsmul_eq_mul, mul_one]
    linear_combination hzw
  · rintro ⟨n, hn⟩
    change n • (1 : ℂ) = z.val - w.val at hn
    rw [zsmul_eq_mul, mul_one] at hn
    refine ⟨⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (n : ℂ),
      (stableTranslationGroup_mem _).mpr ⟨n, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (n : ℂ)).val (w.val :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (z.val :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
    congr 1
    linear_combination hn

/-- The genuine period-one parabolic cusp quotient is homeomorphic to the actual
punctured disc, with its ordinary complex topology. -/
def stableCuspQuotientHomeomorph (h : ℝ) :
    MobiusDomainQuotient (stableCuspDomain h) ≃ₜ stableCuspPuncturedDisc h := by
  let F : C(stableCuspHalfPlane h, stableCuspPuncturedDisc h) :=
    ⟨stableCuspExponential h, stableCuspExponential_continuous h⟩
  have hF : IsQuotientMap F := (stableCuspExponential_isOpenQuotientMap h).isQuotientMap
  exact ((Homeomorph.Quotient.congr (rX := Setoid.ker F) (stableCuspHalfPlaneHomeomorph h)
    (fun z w => (stableCuspDomain_orbitRel_iff h z w).symm)).symm).trans hF.homeomorph

/-- The actual parabolic cusp action satisfies the original compact-hit discontinuity
condition, inherited from the genuine full-plane period-one action. -/
theorem stableCuspDomain_discontinuous (h : ℝ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn stableTranslationGroup (stableCuspDomain h).carrier := by
  intro K hK hKS
  apply stableTranslationDomain_discontinuous K hK
  intro p hp
  obtain ⟨z, _hz, rfl⟩ := hKS hp
  exact ⟨z, rfl⟩

/-- The actual cusp group has no elliptic nonidentity elements. -/
theorem stableCuspGroup_noElliptic (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : f ∈ stableTranslationGroup) (hn : f ≠ 1) : ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f := by
  obtain ⟨n, rfl⟩ := (stableTranslationGroup_mem f).mp hf
  have hb : (n : ℂ) ≠ 0 := by
    intro he
    apply hn
    rw [he]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_eq_one_iff 0).mpr rfl
  intro hE
  exact hE.not_parabolic ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff (n :
    ℂ)).mpr hb)

/-- The actual punctured-disc model is connected in its ordinary complex topology. -/
theorem stableCuspPuncturedDisc_isConnected (h : ℝ) : IsConnected (stableCuspPuncturedDisc h) := by
  let : ConnectedSpace (stableCuspHalfPlane h) := Subtype.connectedSpace (stableCuspHalfPlane_isConnected h)
  have hc : Continuous (fun z : stableCuspHalfPlane h => complexPeriodExponential 1 z.val) :=
    (complexPeriodExponential 1).continuous.comp continuous_subtype_val
  have hr : Set.range (fun z : stableCuspHalfPlane h => complexPeriodExponential 1 z.val) =
      stableCuspPuncturedDisc h := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact (stableCuspExponential h z).property
    · intro hw
      obtain ⟨z, hz⟩ := stableCuspExponential_surjective h ⟨w, hw⟩
      exact ⟨z, congrArg Subtype.val hz⟩
  exact hr ▸ isConnected_range hc

/-- The normalized finite half-plane has its genuine inherited complex-plane atlas. -/
def stableCuspHalfPlaneRiemannSurface (h : ℝ) : RiemannSurface (stableCuspHalfPlane h) where
  toRiemannAtlas := complexPlaneRiemannSurface.toRiemannAtlas.liftLocalHomeomorph
    (Subtype.val : stableCuspHalfPlane h → ℂ)
    (isOpen_lt continuous_const Complex.continuous_im).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  t2Space := inferInstance
  connectedSpace := Subtype.connectedSpace (stableCuspHalfPlane_isConnected h)

/-- The punctured disc has the genuine atlas inherited from the standard punctured plane. -/
def stableCuspPuncturedDiscRiemannSurface (h : ℝ) : RiemannSurface (stableCuspPuncturedDisc h) where
  toRiemannAtlas := puncturedPlaneRiemannSurface.toRiemannAtlas.liftLocalHomeomorph
    (Subtype.val : stableCuspPuncturedDisc h → {z : ℂ // z ≠ 0})
    (stableCuspPuncturedDisc_isOpen h).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  t2Space := inferInstance
  connectedSpace := Subtype.connectedSpace (stableCuspPuncturedDisc_isConnected h)

/-- The finite chart identifies the actual sphere cusp analytically with its finite
half-plane, for the original inherited atlases. -/
theorem stableCuspHalfPlaneHomeomorph_analytic (h : ℝ) :
    RiemannAnalyticMap (stableCuspHalfPlaneRiemannSurface h).toRiemannAtlas
      (mobiusDomainRiemannSurface (stableCuspDomain h)).toRiemannAtlas (stableCuspHalfPlaneHomeomorph h) := by
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.liftLocalHomeomorph
    (Subtype.val : stableCuspHalfPlane h → ℂ)
    (Subtype.val : (stableCuspDomain h).carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (isOpen_lt continuous_const Complex.continuous_im).isOpenEmbedding_subtypeVal.isLocalHomeomorph
    (stableCuspSphere_isOpen h).isOpenEmbedding_subtypeVal.isLocalHomeomorph
    ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (stableCuspHalfPlaneHomeomorph
      h) complexPlane_coe_analytic
    (stableCuspHalfPlaneHomeomorph h).continuous
  intro z
  rfl

/-- The actual exponential is analytic in the ordinary inherited half-plane and punctured-disc atlases. -/
theorem stableCuspExponential_analytic (h : ℝ) :
    RiemannAnalyticMap (stableCuspHalfPlaneRiemannSurface h).toRiemannAtlas
      (stableCuspPuncturedDiscRiemannSurface h).toRiemannAtlas (stableCuspExponential h) := by
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.liftLocalHomeomorph
    (Subtype.val : stableCuspHalfPlane h → ℂ)
    (Subtype.val : stableCuspPuncturedDisc h → {z : ℂ // z ≠ 0})
    (isOpen_lt continuous_const Complex.continuous_im).isOpenEmbedding_subtypeVal.isLocalHomeomorph
    (stableCuspPuncturedDisc_isOpen h).isOpenEmbedding_subtypeVal.isLocalHomeomorph
    (complexPeriodExponential 1) (stableCuspExponential h) (complexPeriodExponential_analytic 1)
    (stableCuspExponential_continuous h)
  intro z
  rfl

/-- The genuine quotient coordinate is exactly the original exponential of a finite cusp representative. -/
theorem stableCuspQuotientHomeomorph_projection (h : ℝ) (z : (stableCuspDomain h).carrier) :
    stableCuspQuotientHomeomorph h (mobiusDomainProjection (stableCuspDomain h) z) =
      stableCuspExponential h ((stableCuspHalfPlaneHomeomorph h).symm z) := rfl

/-- The actual parabolic cusp quotient homeomorphism is analytic for the genuine
original quotient atlas and the ordinary punctured-disc atlas. -/
theorem stableCuspQuotientHomeomorph_analytic (h : ℝ) :
    RiemannAnalyticMap
      (mobiusQuotientRiemannSurface (stableCuspDomain h) (stableCuspDomain_discontinuous h)).toRiemannAtlas
      (stableCuspPuncturedDiscRiemannSurface h).toRiemannAtlas (stableCuspQuotientHomeomorph h) := by
  have hp := mobiusDomainProjection_analytic (stableCuspDomain h) (stableCuspDomain_discontinuous h)
  have hpl := (mobiusDomain_noElliptic_covering (stableCuspDomain h) (stableCuspDomain_discontinuous h)
    stableCuspGroup_noElliptic).isCoveringMap.isLocalHomeomorph
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_surjective_localHomeomorph hp hpl
    (mobiusDomainProjection_surjective (stableCuspDomain h)) (stableCuspQuotientHomeomorph h).continuous
  have hi := riemannAnalyticMap_homeomorph_symm (stableCuspHalfPlaneHomeomorph h)
    (stableCuspHalfPlaneHomeomorph_analytic h)
  have hc := (stableCuspExponential_analytic h).comp hi
  have he : (stableCuspQuotientHomeomorph h) ∘ mobiusDomainProjection (stableCuspDomain h) =
      (stableCuspExponential h) ∘ (stableCuspHalfPlaneHomeomorph h).symm := by
    funext z
    exact stableCuspQuotientHomeomorph_projection h z
  rw [he]
  exact hc

/-- The actual period-one cusp quotient is conformally the genuine punctured disc. -/
theorem stableCuspQuotient_conformallyEquivalent (h : ℝ) :
    RiemannConformallyEquivalent
      (mobiusQuotientRiemannSurface (stableCuspDomain h) (stableCuspDomain_discontinuous h))
      (stableCuspPuncturedDiscRiemannSurface h) :=
  ⟨stableCuspQuotientHomeomorph h, stableCuspQuotientHomeomorph_analytic h,
    (stableCuspQuotientHomeomorph h).bijective⟩

/-- Equal actual groups and equal original domains give the same quotient complex
structure, independently of proofs of openness, invariance and discontinuity. -/
theorem stableCusp_domain_data_conformallyEquivalent
    (H K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hHK : H = K)
    (D : MobiusInvariantDomain H) (E : MobiusInvariantDomain K)
    (hcarrier : D.carrier = E.carrier)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H D.carrier) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn K E.carrier) :
    RiemannConformallyEquivalent (mobiusQuotientRiemannSurface D hD) (mobiusQuotientRiemannSurface E hE) := by
  subst K
  have hDE : D = E := by
    cases D
    cases E
    cases hcarrier
    rfl
  subst E
  exact ⟨id, _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.id _, Function.bijective_id⟩

/-- The normalized punctured-disc conclusion for an actual stable cusp inside any
original Mobius domain. No condition on the full cusp stabilizer is needed here. -/
theorem normalized_cusp_quotient_conformal_punctured_disc {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (h : ℝ)
    (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup) :
    ∃ hSo : IsOpen S.carrier, ∃ hSc : IsConnected S.carrier,
      RiemannConformallyEquivalent (S.openImageRiemannSurface hD hSo hSc)
        (stableCuspPuncturedDiscRiemannSurface h) := by
  have hSo : IsOpen S.carrier := hS ▸ stableCuspSphere_isOpen h
  have hSc : IsConnected S.carrier := hS ▸ stableCuspSphere_isConnected h
  refine ⟨hSo, hSc, ?_⟩
  have he := stableCusp_domain_data_conformallyEquivalent S.stabilizer stableTranslationGroup hK
    (S.openDomain hSo hSc) (stableCuspDomain h) hS
    (S.openDomain_discontinuous hD hSo hSc) (stableCuspDomain_discontinuous h)
  exact (mobius_stable_quotient_conformallyEquivalent S hD hSo hSc).symm.trans
    (he.trans (stableCuspQuotient_conformallyEquivalent h))

/-- The genuine filled target disc, including the missing exponential value zero. -/
def stableCuspFilledDisc (h : ℝ) : Set ℂ := Metric.ball 0 (stableCuspRadius h)

/-- The finite exponential into the filled disc with its ordinary complex topology. -/
def stableCuspFiniteToFilledDisc (h : ℝ) : C(stableCuspHalfPlane h, stableCuspFilledDisc h) where
  toFun z := ⟨(complexPeriodExponential 1 z.val).val, by
    simpa only [stableCuspFilledDisc, Metric.mem_ball, dist_zero_right] using
      (stableCuspExponential_mem h z.val).mpr z.property⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp ((complexPeriodExponential 1).continuous.comp continuous_subtype_val)) _

/-- Add exactly one actual cusp point to the original finite horodisc; its topology
will be the height-tail topology, rather than the compactification topology. -/
def StableCuspCompletion (h : ℝ) := Option (stableCuspHalfPlane h)

/-- The original finite inclusion, with the completed cusp as its declared target. -/
def stableCuspCompletionSome (h : ℝ) : stableCuspHalfPlane h → StableCuspCompletion h := some

theorem stableCuspCompletionSome_injective (h : ℝ) : Function.Injective (stableCuspCompletionSome h) :=
  Option.some_injective _

/-- The named added ideal point retains its declared completed-cusp type. -/
def stableCuspCompletionInfinity (h : ℝ) : StableCuspCompletion h := none

/-- The exponential fills the missing value at the added cusp. -/
def stableCuspCompletionToDisc (h : ℝ) : StableCuspCompletion h → stableCuspFilledDisc h :=
  Option.rec ⟨0, by simpa only [stableCuspFilledDisc, Metric.mem_ball, dist_self] using stableCuspRadius_pos h⟩
    (stableCuspFiniteToFilledDisc h)

/-- Finite ordinary open sets together with inverse images of ordinary filled-disc
open sets generate exactly the normalized height-tail cusp topology. -/
def stableCuspCompletionBasis (h : ℝ) : Set (Set (StableCuspCompletion h)) :=
  {U | (∃ V : Set (stableCuspHalfPlane h), IsOpen V ∧ (stableCuspCompletionSome h) '' V = U) ∨
    ∃ V : Set (stableCuspFilledDisc h), IsOpen V ∧ stableCuspCompletionToDisc h ⁻¹' V = U}

instance stableCuspCompletionTopology (h : ℝ) : TopologicalSpace (StableCuspCompletion h) :=
  TopologicalSpace.generateFrom (stableCuspCompletionBasis h)

/-- The finite exponential remains open when viewed in the ordinary filled disc. -/
theorem stableCuspFiniteToFilledDisc_isOpenMap (h : ℝ) : IsOpenMap (stableCuspFiniteToFilledDisc h) := by
  have ho : IsOpenMap (fun z : stableCuspPuncturedDisc h => (z.val : ℂ)) :=
    (show IsOpen ({z : ℂ | z ≠ 0}) from isClosed_singleton.isOpen_compl).isOpenEmbedding_subtypeVal.isOpenMap.comp
      (stableCuspPuncturedDisc_isOpen h).isOpenEmbedding_subtypeVal.isOpenMap
  exact (ho.comp (stableCuspExponential_isOpenQuotientMap h).isOpenMap).codRestrict _

/-- This generating family is closed under actual binary intersections. -/
theorem stableCuspCompletionBasis_inter (h : ℝ) {U V : Set (StableCuspCompletion h)}
    (hU : U ∈ stableCuspCompletionBasis h) (hV : V ∈ stableCuspCompletionBasis h) :
    U ∩ V ∈ stableCuspCompletionBasis h := by
  rcases hU with ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
  · rcases hV with ⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩
    · exact Or.inl ⟨A ∩ B, hA.inter hB, image_inter (stableCuspCompletionSome_injective h)⟩
    · refine Or.inl ⟨A ∩ stableCuspFiniteToFilledDisc h ⁻¹' B,
        hA.inter (hB.preimage (stableCuspFiniteToFilledDisc h).continuous), ?_⟩
      change (stableCuspCompletionSome h) ''
        (A ∩ (stableCuspCompletionSome h) ⁻¹' (stableCuspCompletionToDisc h ⁻¹' B)) = _
      exact image_inter_preimage _ _ _
  · rcases hV with ⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩
    · refine Or.inl ⟨B ∩ stableCuspFiniteToFilledDisc h ⁻¹' A,
        hB.inter (hA.preimage (stableCuspFiniteToFilledDisc h).continuous), ?_⟩
      change (stableCuspCompletionSome h) ''
        (B ∩ (stableCuspCompletionSome h) ⁻¹' (stableCuspCompletionToDisc h ⁻¹' A)) = _
      exact (image_inter_preimage _ _ _).trans (inter_comm _ _)
    · exact Or.inr ⟨A ∩ B, hA.inter hB, rfl⟩

/-- The actual cusp topology has the displayed basis, not merely a named generating family. -/
theorem stableCuspCompletionBasis_isBasis (h : ℝ) :
    IsTopologicalBasis (stableCuspCompletionBasis h) := by
  have hu : (Set.univ : Set (StableCuspCompletion h)) ∈ stableCuspCompletionBasis h :=
    Or.inr ⟨Set.univ, isOpen_univ, preimage_univ⟩
  have hb := isTopologicalBasis_of_subbasis_of_inter
    (t := stableCuspCompletionTopology h) rfl (fun _ hU _ hV => stableCuspCompletionBasis_inter h hU hV)
  simpa only [insert_eq_of_mem hu] using hb

/-- The original finite cusp embeds openly with its original topology. -/
theorem stableCuspCompletion_some_isOpenEmbedding (h : ℝ) :
    Topology.IsOpenEmbedding (stableCuspCompletionSome h) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · apply continuous_generateFrom_iff.mpr
    intro U hU
    rcases hU with ⟨V, hV, rfl⟩ | ⟨V, hV, rfl⟩
    · simpa only [preimage_image_eq _ (stableCuspCompletionSome_injective h)] using hV
    · exact hV.preimage (stableCuspFiniteToFilledDisc h).continuous
  · exact stableCuspCompletionSome_injective h
  · intro U hU
    exact TopologicalSpace.isOpen_generateFrom_of_mem (Or.inl ⟨U, hU, rfl⟩)

/-- The filled exponential is continuous in the actual generated cusp topology. -/
theorem stableCuspCompletionToDisc_continuous (h : ℝ) : Continuous (stableCuspCompletionToDisc h) := by
  apply continuous_def.mpr
  intro U hU
  exact TopologicalSpace.isOpen_generateFrom_of_mem (Or.inr ⟨U, hU, rfl⟩)

/-- Filling adds precisely the missing value zero; every ordinary disc point has a representative. -/
theorem stableCuspCompletionToDisc_surjective (h : ℝ) : Function.Surjective (stableCuspCompletionToDisc h) := by
  intro w
  by_cases hw : w.val = 0
  · exact ⟨none, Subtype.ext hw.symm⟩
  · have hwm : (⟨w.val, hw⟩ : {z : ℂ // z ≠ 0}) ∈ stableCuspPuncturedDisc h := by
      simpa only [stableCuspPuncturedDisc, mem_ofPred_eq, stableCuspFilledDisc,
        Metric.mem_ball, dist_zero_right] using w.property
    obtain ⟨z, hz⟩ := stableCuspExponential_surjective h ⟨⟨w.val, hw⟩, hwm⟩
    refine ⟨some z, Subtype.ext ?_⟩
    exact congrArg (fun a : stableCuspPuncturedDisc h => (a.val : ℂ)) hz

/-- The genuine filled exponential is open for the exact cusp topology. -/
theorem stableCuspCompletionToDisc_isOpenMap (h : ℝ) : IsOpenMap (stableCuspCompletionToDisc h) := by
  apply (stableCuspCompletionBasis_isBasis h).isOpenMap_iff.mpr
  intro U hU
  rcases hU with ⟨V, hV, rfl⟩ | ⟨V, hV, rfl⟩
  · rw [image_image]
    exact stableCuspFiniteToFilledDisc_isOpenMap h V hV
  · rw [image_preimage_eq _ (stableCuspCompletionToDisc_surjective h)]
    exact hV

/-- The actual generated cusp topology makes filling a genuine open quotient map. -/
theorem stableCuspCompletionToDisc_isOpenQuotientMap (h : ℝ) :
    IsOpenQuotientMap (stableCuspCompletionToDisc h) :=
  ⟨stableCuspCompletionToDisc_surjective h, stableCuspCompletionToDisc_continuous h,
    stableCuspCompletionToDisc_isOpenMap h⟩

/-- The completed cusp consists of the original finite points and the actual ideal
point infinity; this is an injective map of the underlying sets. -/
def stableCuspCompletionSphere (h :
  ℝ) : StableCuspCompletion h → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  Option.rec ∞ (fun z => (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))

theorem stableCuspCompletionSphere_injective (h : ℝ) : Function.Injective (stableCuspCompletionSphere h) := by
  intro p q hpq
  cases p with
  | none =>
    cases q with
    | none => rfl
    | some z => exact False.elim ((OnePoint.coe_ne_infty z.val) hpq.symm)
  | some z =>
    cases q with
    | none => exact False.elim ((OnePoint.coe_ne_infty z.val) hpq)
    | some w =>
      exact congrArg some (Subtype.ext (OnePoint.coe_injective hpq))

/-- Fibers of the filled exponential are exactly the original actual parabolic
Mobius orbits, including the unique new ideal-point orbit. -/
theorem stableCuspCompletion_orbitRel_iff (h : ℝ) (p q : StableCuspCompletion h) :
    (MulAction.orbitRel stableTranslationGroup _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      (stableCuspCompletionSphere h p) (stableCuspCompletionSphere h q) ↔
      stableCuspCompletionToDisc h p = stableCuspCompletionToDisc h q := by
  cases p with
  | none =>
    cases q with
    | none =>
      constructor
      · intro _; rfl
      · intro _; exact ⟨1, rfl⟩
    | some z =>
      constructor
      · rintro ⟨g, hg⟩
        obtain ⟨n, hn⟩ := (stableTranslationGroup_mem g.val).mp g.property
        change g.val.val (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ∞ at hg
        rw [hn, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe] at hg
        exact False.elim (OnePoint.coe_ne_infty _ hg)
      · intro he
        have hz : (stableCuspCompletionToDisc h (some z)).val ≠ 0 :=
          (complexPeriodExponential 1 z.val).property
        exact False.elim (hz (congrArg Subtype.val he).symm)
  | some z =>
    cases q with
    | none =>
      constructor
      · rintro ⟨g, hg⟩
        obtain ⟨n, hn⟩ := (stableTranslationGroup_mem g.val).mp g.property
        change g.val.val ∞ = (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hg
        rw [hn, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty] at hg
        exact False.elim (OnePoint.coe_ne_infty _ hg.symm)
      · intro he
        have hz : (stableCuspCompletionToDisc h (some z)).val ≠ 0 :=
          (complexPeriodExponential 1 z.val).property
        exact False.elim (hz (congrArg Subtype.val he))
    | some w =>
      constructor
      · rintro ⟨g, hg⟩
        have ho : MulAction.orbitRel stableTranslationGroup (stableCuspDomain h).carrier
            (stableCuspHalfPlaneHomeomorph h z) (stableCuspHalfPlaneHomeomorph h w) :=
          ⟨g, Subtype.ext hg⟩
        have he := (stableCuspDomain_orbitRel_iff h z w).mp ho
        exact Subtype.ext (congrArg (fun a : stableCuspPuncturedDisc h => (a.val : ℂ)) he)
      · intro he
        have hz : stableCuspExponential h z = stableCuspExponential h w :=
          Subtype.ext (Subtype.ext (congrArg (fun a : stableCuspFilledDisc h => a.val) he))
        obtain ⟨g, hg⟩ := (stableCuspDomain_orbitRel_iff h z w).mpr hz
        exact ⟨g, congrArg Subtype.val hg⟩

/-- The original actual parabolic-orbit quotient of the completed cusp has exactly
the ordinary filled-disc topology. -/
def stableCuspCompletionQuotientHomeomorph (h : ℝ) :
    _root_.Quotient ((MulAction.orbitRel stableTranslationGroup
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap
      (stableCuspCompletionSphere h)) ≃ₜ stableCuspFilledDisc h := by
  let F : C(StableCuspCompletion h, stableCuspFilledDisc h) :=
    ⟨stableCuspCompletionToDisc h, stableCuspCompletionToDisc_continuous h⟩
  have hF : IsQuotientMap F := (stableCuspCompletionToDisc_isOpenQuotientMap h).isQuotientMap
  exact (Homeomorph.Quotient.congrRight (fun p q => stableCuspCompletion_orbitRel_iff h p q)).trans hF.homeomorph

/-- A height tail, written intrinsically as the actual filled-coordinate ball preimage. -/
def stableCuspCompletionTail (h t : ℝ) : Set (StableCuspCompletion h) :=
  stableCuspCompletionToDisc h ⁻¹' {z | ‖z.val‖ < stableCuspRadius t}

theorem stableCuspCompletionTail_isOpen (h t : ℝ) : IsOpen (stableCuspCompletionTail h t) :=
  (isOpen_lt continuous_subtype_val.norm continuous_const).preimage
    (stableCuspCompletionToDisc_continuous h)

theorem stableCuspCompletionTail_none (h t : ℝ) : stableCuspCompletionInfinity h ∈ stableCuspCompletionTail h t := by
  change ‖(0 : ℂ)‖ < stableCuspRadius t
  simpa only [norm_zero] using stableCuspRadius_pos t

/-- The generated cusp neighborhoods are the literal horizontal height tails. -/
theorem stableCuspCompletionTail_some (h t : ℝ) (z : stableCuspHalfPlane h) :
    stableCuspCompletionSome h z ∈ stableCuspCompletionTail h t ↔ t < z.val.im := by
  exact stableCuspExponential_mem t z.val

/-- Every original cusp neighborhood contains a literal uniform horizontal height tail. -/
theorem stableCuspCompletion_mem_nhds_iff (h : ℝ) (U : Set (StableCuspCompletion h)) :
    U ∈ 𝓝 (stableCuspCompletionInfinity h) ↔ ∃ t : ℝ, h < t ∧ stableCuspCompletionTail h t ⊆ U := by
  constructor
  · intro hU
    obtain ⟨B, hB, hnB, hBU⟩ := (stableCuspCompletionBasis_isBasis h).mem_nhds_iff.mp hU
    rcases hB with ⟨V, _hV, rfl⟩ | ⟨V, hV, rfl⟩
    · obtain ⟨z, _hz, he⟩ := hnB
      change some z = none at he
      cases he
    · have hzero : stableCuspCompletionToDisc h none ∈ V := hnB
      obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hzero)
      let t : ℝ := max (h + 1) (-Real.log ε / (2 * Real.pi) + 1)
      have hπ : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
      have htH : h < t := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hlog : -2 * Real.pi * t < Real.log ε := by
        have ht := le_max_right (h + 1) (-Real.log ε / (2 * Real.pi) + 1)
        have he : (-Real.log ε / (2 * Real.pi)) * (2 * Real.pi) = -Real.log ε :=
          div_mul_cancel₀ _ hπ.ne'
        nlinarith
      have htε : stableCuspRadius t < ε := (Real.lt_log_iff_exp_lt hε).mp hlog
      refine ⟨t, htH, fun p hp => hBU (hεV ?_)⟩
      change dist (stableCuspCompletionToDisc h p) (stableCuspCompletionToDisc h none) < ε
      have hpε : ‖(stableCuspCompletionToDisc h p).val‖ < ε := lt_trans hp htε
      simpa only [Subtype.dist_eq, stableCuspCompletionToDisc, Option.rec, dist_zero_right] using hpε
  · rintro ⟨t, _ht, htU⟩
    exact mem_of_superset ((stableCuspCompletionTail_isOpen h t).mem_nhds
      (stableCuspCompletionTail_none h t)) htU

/-- The added ideal point has no compact neighborhood in the genuine height-tail
topology. A fixed-height infinite translation fiber lies in every sufficiently deep
tail, while compactness would bound all its original finite coordinates. -/
theorem stableCuspCompletion_no_compact_nhds (h : ℝ) :
    ¬∃ K : Set (StableCuspCompletion h), IsCompact K ∧ K ∈ 𝓝 (stableCuspCompletionInfinity h) := by
  rintro ⟨K, hK, hKn⟩
  obtain ⟨t, ht, htK⟩ := (stableCuspCompletion_mem_nhds_iff h K).mp hKn
  let y : ℝ := t + 1
  have hy : h < y := by dsimp [y]; linarith
  let z₀ : stableCuspHalfPlane h := ⟨(⟨0, y⟩ : ℂ), hy⟩
  let w₀ := stableCuspFiniteToFilledDisc h z₀
  let C : Set (StableCuspCompletion h) := stableCuspCompletionToDisc h ⁻¹' {w₀}
  have hw₀ : w₀.val ≠ 0 := (complexPeriodExponential 1 z₀.val).property
  have hw₀t : ‖w₀.val‖ < stableCuspRadius t :=
    (stableCuspExponential_mem t z₀.val).mpr (by change t < y; dsimp [y]; linarith)
  have hCK : C ⊆ K := by
    intro p hp
    apply htK
    change ‖(stableCuspCompletionToDisc h p).val‖ < stableCuspRadius t
    have he : stableCuspCompletionToDisc h p = w₀ := hp
    rw [he]
    exact hw₀t
  have hCc : IsClosed C := isClosed_singleton.preimage (stableCuspCompletionToDisc_continuous h)
  have hCcpt : IsCompact C := by
    have he : K ∩ C = C := inter_eq_right.mpr hCK
    exact he ▸ hK.inter_right hCc
  have hCfinite : C ⊆ Set.range (stableCuspCompletionSome h) := by
    intro p hp
    cases p with
    | none =>
      have he : (0 : ℂ) = w₀.val := congrArg (fun w : stableCuspFilledDisc h => w.val) hp
      exact False.elim (hw₀ he.symm)
    | some z => exact ⟨z, rfl⟩
  let A : Set (stableCuspHalfPlane h) := stableCuspCompletionSome h ⁻¹' C
  let E : A ≃ₜ C := (stableCuspCompletion_some_isOpenEmbedding h).isEmbedding.homeomorphOfSubsetRange hCfinite
  let : CompactSpace C := isCompact_iff_compactSpace.mp hCcpt
  let : CompactSpace A := E.symm.compactSpace
  have hbounded : IsCompact (Set.range (fun z : A => z.val.val)) :=
    isCompact_range (continuous_subtype_val.comp continuous_subtype_val)
  obtain ⟨R, _hRpos, hR⟩ := hbounded.isBounded.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt R
  let zN : stableCuspHalfPlane h := ⟨(N : ℂ) + Complex.I * (y : ℂ), by
    simpa only [stableCuspHalfPlane, mem_ofPred_eq, Complex.add_im, Complex.natCast_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, zero_add] using hy⟩
  have hdiff : zN.val - z₀.val = (N : ℂ) := by
    apply Complex.ext <;> simp [zN, z₀, Complex.mul_re, Complex.mul_im]
  have he : complexPeriodExponential 1 zN.val = complexPeriodExponential 1 z₀.val := by
    rw [complexPeriodExponential_fiber_iff 1 one_ne_zero]
    refine ⟨(N : ℤ), ?_⟩
    change (N : ℤ) • (1 : ℂ) = zN.val - z₀.val
    rw [hdiff, zsmul_eq_mul, mul_one, Int.cast_natCast]
  have hzNA : zN ∈ A := by
    change stableCuspCompletionToDisc h (stableCuspCompletionSome h zN) = w₀
    exact Subtype.ext (congrArg (fun w : {z : ℂ // z ≠ 0} => w.val) he)
  have hb : ‖zN.val‖ ≤ R := hR zN.val ⟨⟨zN, hzNA⟩, rfl⟩
  have hre : zN.val.re = (N : ℝ) := by simp [zN, Complex.mul_re]
  have hle := Complex.abs_re_le_norm zN.val
  rw [hre, abs_of_nonneg (Nat.cast_nonneg N)] at hle
  exact (not_lt_of_ge (hle.trans hb)) hN

/-- In particular this is not a locally compact space, despite its ordinary-disc quotient. -/
theorem stableCuspCompletion_not_locallyCompact (h : ℝ) : ¬LocallyCompactSpace (StableCuspCompletion h) := by
  intro hc
  let : LocallyCompactSpace (StableCuspCompletion h) := hc
  exact stableCuspCompletion_no_compact_nhds h (exists_compact_mem_nhds (stableCuspCompletionInfinity h))

/-- Equal original domain data give the canonical identity-on-representatives quotient homeomorphism. -/
def stableCuspDomainDataHomeomorph
    (H K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hHK : H = K)
    (D : MobiusInvariantDomain H) (E : MobiusInvariantDomain K)
    (hcarrier : D.carrier = E.carrier) : MobiusDomainQuotient D ≃ₜ MobiusDomainQuotient E := by
  subst K
  have hDE : D = E := by cases D; cases E; cases hcarrier; rfl
  subst E
  exact Homeomorph.refl _

/-- This actual data identification preserves every original projected representative. -/
theorem stableCuspDomainDataHomeomorph_projection
    (H K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hHK : H = K)
    (D : MobiusInvariantDomain H) (E : MobiusInvariantDomain K)
    (hcarrier : D.carrier = E.carrier) (z : D.carrier) :
    stableCuspDomainDataHomeomorph H K hHK D E hcarrier (mobiusDomainProjection D z) =
      mobiusDomainProjection E ⟨z.val, hcarrier ▸ z.property⟩ := by
  subst K
  have hDE : D = E := by cases D; cases E; cases hcarrier; rfl
  subst E
  rfl

/-- The canonical data homeomorphism is analytic for the original quotient atlases. -/
theorem stableCuspDomainDataHomeomorph_analytic
    (H K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hHK : H = K)
    (D : MobiusInvariantDomain H) (E : MobiusInvariantDomain K)
    (hcarrier : D.carrier = E.carrier)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H D.carrier) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn K E.carrier) :
    RiemannAnalyticMap (mobiusQuotientRiemannSurface D hD).toRiemannAtlas
      (mobiusQuotientRiemannSurface E hE).toRiemannAtlas
      (stableCuspDomainDataHomeomorph H K hHK D E hcarrier) := by
  subst K
  have hDE : D = E := by cases D; cases E; cases hcarrier; rfl
  subst E
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.id _

/-- The actual canonical punctured-disc coordinate on the full-group stable cusp image. -/
def stableCuspImageHomeomorph {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ)
    (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    S.quotientImage ≃ₜ stableCuspPuncturedDisc h :=
  (S.openDomainImageHomeomorph hSo hSc).symm.trans
    ((stableCuspDomainDataHomeomorph S.stabilizer stableTranslationGroup hK
      (S.openDomain hSo hSc) (stableCuspDomain h) hS).trans (stableCuspQuotientHomeomorph h))

/-- This image coordinate is analytic for the genuine inherited full-quotient atlas. -/
theorem stableCuspImageHomeomorph_analytic {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (h : ℝ)
    (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    RiemannAnalyticMap (S.openImageRiemannSurface hD hSo hSc).toRiemannAtlas
      (stableCuspPuncturedDiscRiemannSurface h).toRiemannAtlas
      (stableCuspImageHomeomorph S h hS hK hSo hSc) := by
  have hi := riemannAnalyticMap_homeomorph_symm (S.openDomainImageHomeomorph hSo hSc)
    (S.openDomainImageHomeomorph_analytic hD hSo hSc)
  have hd := stableCuspDomainDataHomeomorph_analytic S.stabilizer stableTranslationGroup hK
    (S.openDomain hSo hSc) (stableCuspDomain h) hS
    (S.openDomain_discontinuous hD hSo hSc) (stableCuspDomain_discontinuous h)
  exact ((stableCuspQuotientHomeomorph_analytic h).comp hd).comp hi

/-- The canonical image coordinate is the literal exponential of every original finite cusp representative. -/
theorem stableCuspImageHomeomorph_projection {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ)
    (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (w : S.carrier) (z : stableCuspHalfPlane h) (hw : w.val = (z.val :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    stableCuspImageHomeomorph S h hS hK hSo hSc
      (mobiusDiscRangeProjection D S.carrier S.subset_domain w) = stableCuspExponential h z := by
  have hproj : S.openDomainImageHomeomorph hSo hSc
      (mobiusDomainProjection (S.openDomain hSo hSc) w) =
      mobiusDiscRangeProjection D S.carrier S.subset_domain w := by
    apply Subtype.ext
    exact (S.openDomainImageHomeomorph_coe hSo hSc _).trans
      (S.openDomainQuotientMap_projection hSo hSc w)
  rw [← hproj]
  simp only [stableCuspImageHomeomorph, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  have hd := stableCuspDomainDataHomeomorph_projection S.stabilizer stableTranslationGroup hK
    (S.openDomain hSo hSc) (stableCuspDomain h) hS w
  let wE : (stableCuspDomain h).carrier := ⟨w.val, by
    change w.val ∈ stableCuspSphere h
    rw [← hS]
    exact w.property⟩
  have hp := stableCuspQuotientHomeomorph_projection h wE
  refine (congrArg (stableCuspQuotientHomeomorph h) hd).trans (hp.trans ?_)
  apply congrArg (stableCuspExponential h)
  apply (stableCuspHalfPlaneHomeomorph h).injective
  rw [Homeomorph.apply_symm_apply]
  exact Subtype.ext hw


end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius

/-- The boundary of any genuine disc preserved by unit translation is a literal
horizontal extended line; infinity and the finite-line coefficients are derived. -/
theorem parabolicTranslationDisc_frontier_horizontal {D : Set
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (hD : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D)
    (hp : (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 : Equiv.Perm
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D = D) :
    ∃ h : ℝ, frontier D = _root_.LowDimensionalTopology.Geometry.Mobius.complexLine Complex.I h := by
  have hinfty : ∞ ∈ frontier D := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_fixed_mem_disc_frontier
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
      1) ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff 1).mpr one_ne_zero)
    hD hp (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1)
  rcases (_root_.LowDimensionalTopology.Geometry.Mobius.isComplexGeneralizedCircle_iff (frontier D)).mp
    (_root_.LowDimensionalTopology.Geometry.Mobius.complexDisc_frontier_isGeneralized hD) with ⟨c, r, _, he⟩ | ⟨a, t,
      ha, he⟩
  · rw [he] at hinfty
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_infty c r hinfty).elim
  · have hstable : (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 : Equiv.Perm
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' frontier D =
        frontier D := by
      have hh := (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)).image_frontier D
      change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 : Equiv.Perm
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' frontier D =
        frontier ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 : Equiv.Perm
          _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D) at hh
      rwa [hp] at hh
    let z : ℂ := (t / ‖a‖ ^ 2) • a
    have hz : inner ℝ z a = t := by
      simp only [z, real_inner_smul_left, real_inner_self_eq_norm_sq]
      exact div_mul_cancel₀ t (pow_ne_zero 2 (norm_ne_zero_iff.mpr ha))
    have hmem : (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ frontier D := by
      rw [he, _root_.LowDimensionalTopology.Geometry.Mobius.complexLine_coe]
      exact hz
    have hm : ((z + 1 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ frontier D := by
      rw [← hstable]
      exact ⟨(z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), hmem,
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe 1 z⟩
    rw [he, _root_.LowDimensionalTopology.Geometry.Mobius.complexLine_coe, inner_add_left, hz] at hm
    have har : a.re = 0 := by
      have hr : inner ℝ (1 : ℂ) a = 0 := by linarith
      simpa [Complex.inner] using hr
    have hai : a.im ≠ 0 := by
      intro hai
      exact ha (Complex.ext (by simpa using har) (by simpa using hai))
    refine ⟨t / a.im, he.trans ?_⟩
    ext w
    induction w using OnePoint.rec with
    | infty => simp only [_root_.LowDimensionalTopology.Geometry.Mobius.complexLine_infty]
    | coe w =>
      rw [_root_.LowDimensionalTopology.Geometry.Mobius.complexLine_coe,
        _root_.LowDimensionalTopology.Geometry.Mobius.complexLine_coe]
      have hw : inner ℝ w a = w.im * a.im := by simp [Complex.inner, har, mul_comm]
      have hi : inner ℝ w Complex.I = w.im := by simp [Complex.inner]
      rw [hw, hi]
      exact (eq_div_iff hai).symm

/-- Any actual generalized-circle disc preserved by unit translation is a literal
upper or lower horizontal half-plane, with no extra side assumption. -/
theorem parabolicTranslationDisc_eq_halfPlane {D : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (hD : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D)
    (hp : (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 : Equiv.Perm
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D = D) :
    ∃ h : ℝ, D = ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {z | h < z.im} ∨
      D = ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {z | z.im < h} := by
  obtain ⟨h, hf⟩ := parabolicTranslationDisc_frontier_horizontal hD hp
  let U : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ((↑) : ℂ →
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {z | h < z.im}
  let L : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ((↑) : ℂ →
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {z | z.im < h}
  have hU : IsOpen U := OnePoint.isOpenEmbedding_coe.isOpenMap _
    (isOpen_lt continuous_const Complex.continuous_im)
  have hL : IsOpen L := OnePoint.isOpenEmbedding_coe.isOpenMap _
    (isOpen_lt Complex.continuous_im continuous_const)
  have hcU : IsPreconnected U := (convex_halfSpace_im_gt h).isPreconnected.image _
    OnePoint.isOpenEmbedding_coe.continuous.continuousOn
  have hcL : IsPreconnected L := (convex_halfSpace_im_lt h).isPreconnected.image _
    OnePoint.isOpenEmbedding_coe.continuous.continuousOn
  have hdis : Disjoint U L := by
    apply Set.disjoint_left.mpr
    rintro z ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
    have huv : v = u := OnePoint.coe_injective he
    subst v
    change h < u.im at hu
    change u.im < h at hv
    exact (lt_asymm hu hv)
  have hunion : (_root_.LowDimensionalTopology.Geometry.Mobius.complexLine Complex.I h)ᶜ = U ∪ L := by
    ext z
    induction z using OnePoint.rec with
    | infty => simp [U, L, _root_.LowDimensionalTopology.Geometry.Mobius.complexLine_infty]
    | coe z =>
      simp only [Set.mem_compl_iff, _root_.LowDimensionalTopology.Geometry.Mobius.complexLine_coe]
      have hi : inner ℝ z Complex.I = z.im := by simp [Complex.inner]
      rw [hi]
      change z.im ≠ h ↔ (∃ u : ℂ, h < u.im ∧ (u : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = z) ∨
        (∃ v : ℂ, v.im < h ∧ (v : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = z)
      simp only [OnePoint.coe_eq_coe, exists_eq_right]
      exact ne_iff_lt_or_gt.trans or_comm
  obtain ⟨z, hz⟩ := hD.isConnected.nonempty
  have hcomp : connectedComponentIn (_root_.LowDimensionalTopology.Geometry.Mobius.complexLine Complex.I h)ᶜ z = D := by
    rw [← hf]
    exact _root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_component_of_open_preconnected hD.isOpen hD.isConnected.isPreconnected hz
  have hsub : D ⊆ U ∪ L := by
    rw [← hunion, ← hcomp]
    exact connectedComponentIn_subset _ _
  refine ⟨h, ?_⟩
  rcases IsPreconnected.subset_or_subset hU hL hdis hsub hD.isConnected.isPreconnected with hu | hl
  · exact Or.inl (hu.antisymm (by
      rw [← hcomp]
      exact hcU.subset_connectedComponentIn (hu hz) (by rw [hunion]; exact Set.subset_union_left)))
  · exact Or.inr (hl.antisymm (by
      rw [← hcomp]
      exact hcL.subset_connectedComponentIn (hl hz) (by rw [hunion]; exact Set.subset_union_right)))


end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A nonzero lower-left coefficient never vanishes in the actual parabolic Jorgensen iteration. -/
theorem stableCuspShimizu_iterate_lowerLeft (B :
  _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) (hc : B 1 0 ≠ 0) (n : ℕ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenIterate _root_.LowDimensionalTopology.Geometry.Mobius.invariantDiscTranslationLift B n 1 0 ≠ 0 := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenStep _root_.LowDimensionalTopology.Geometry.Mobius.invariantDiscTranslationLift (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenIterate _root_.LowDimensionalTopology.Geometry.Mobius.invariantDiscTranslationLift B n) 1 0 ≠ 0
    rw [(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenStep_parabolic _).2.2.1]
    exact neg_ne_zero.mpr (pow_ne_zero 2 ih)

/-- The actual normalized translation lift really is the specified parabolic translation. -/
theorem stableCuspShimizu_translation_projection :
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection _root_.LowDimensionalTopology.Geometry.Mobius.invariantDiscTranslationLift = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 := by
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.invariantDiscTranslationLift_projection]
  apply Subtype.ext
  apply Equiv.ext
  intro p
  induction p using OnePoint.rec with
  | infty => rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement_infty,
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty]
  | coe z =>
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement_coe,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
    simp

/-- The genuine Shimizu lower-left bound for every actual discrete Mobius group
containing the original period-one parabolic. No non-elementary hypothesis is added. -/
theorem stableCuspShimizu_lowerLeft (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B ∈ G) (hc : B 1 0 ≠ 0) :
    1 ≤ ‖B 1 0‖ := by
  let K := G.comap _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection
  let : DiscreteTopology K := _root_.LowDimensionalTopology.Geometry.Mobius.discreteMobius_preimage G hd
  have hAK : _root_.LowDimensionalTopology.Geometry.Mobius.invariantDiscTranslationLift ∈ K := by
    change _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection _root_.LowDimensionalTopology.Geometry.Mobius.invariantDiscTranslationLift ∈ G
    rw [stableCuspShimizu_translation_projection]
    exact hT
  have hne : ∀ n, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenIterate _root_.LowDimensionalTopology.Geometry.Mobius.invariantDiscTranslationLift B n ≠ _root_.LowDimensionalTopology.Geometry.Mobius.invariantDiscTranslationLift := by
    intro n he
    apply stableCuspShimizu_iterate_lowerLeft B hc n
    rw [he]
    rfl
  have hh := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_parabolic_bound K B hAK hB hne
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenMatrixDefect_parabolic] at hh
  nlinarith [norm_nonneg (B 1 0)]

/-- The exact affine-chart difference from the parabolic fixed point for a determinant-one matrix. -/
theorem stableCusp_matrix_difference (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) (z :
  ℂ)
    (hc : B 1 0 ≠ 0) (hd : B 1 0 * z + B 1 1 ≠ 0) :
    (B 0 0 * z + B 0 1) / (B 1 0 * z + B 1 1) - B 0 0 / B 1 0 =
      -1 / (B 1 0 * (B 1 0 * z + B 1 1)) := by
  have hdet : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using B.det_coe
  have hd' : z * B 1 0 + B 1 1 ≠ 0 := by simpa only [mul_comm] using hd
  field_simp [hc, hd, hd']
  linear_combination -hdet

/-- A high cusp point stays uniformly close to the actual finite fixed-point image.
The pole is below the cusp because it is outside the original invariant domain. -/
theorem stableCusp_matrix_distance (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) (h t :
  ℝ) (z : ℂ)
    (hc : 1 ≤ ‖B 1 0‖) (ht : h < t) (hz : t < z.im)
    (hpole : (-(B 1 1) / B 1 0).im ≤ h) :
    B 1 0 * z + B 1 1 ≠ 0 ∧
      dist ((B 0 0 * z + B 0 1) / (B 1 0 * z + B 1 1)) (B 0 0 / B 1 0) < (t - h)⁻¹ := by
  have hcpos : 0 < ‖B 1 0‖ := lt_of_lt_of_le zero_lt_one hc
  have hcn : B 1 0 ≠ 0 := norm_pos_iff.mp hcpos
  have hden : B 1 0 * z + B 1 1 = B 1 0 * (z - (-(B 1 1) / B 1 0)) := by
    field_simp
    ring
  have him : t - h < (z - (-(B 1 1) / B 1 0)).im := by
    rw [Complex.sub_im]
    linarith
  have hnorm : t - h < ‖z - (-(B 1 1) / B 1 0)‖ :=
    lt_of_lt_of_le him (le_trans (le_abs_self _) (Complex.abs_im_le_norm _))
  have hnormpos : 0 < ‖z - (-(B 1 1) / B 1 0)‖ := lt_trans (sub_pos.mpr ht) hnorm
  have hdn : B 1 0 * z + B 1 1 ≠ 0 := by
    rw [hden]
    exact mul_ne_zero hcn (norm_pos_iff.mp hnormpos)
  refine ⟨hdn, ?_⟩
  rw [dist_eq_norm, stableCusp_matrix_difference B z hcn hdn, norm_div,
    norm_neg, norm_one, norm_mul, hden, norm_mul]
  have hm : t - h < ‖B 1 0‖ * (‖B 1 0‖ * ‖z - (-(B 1 1) / B 1 0)‖) := by
    nlinarith [mul_self_nonneg (‖B 1 0‖ - 1)]
  simpa only [one_div] using one_div_lt_one_div_of_lt (sub_pos.mpr ht) hm

/-- The genuine spherical chordal distance is bounded by twice finite Euclidean distance. -/
theorem stableCusp_chordal_le_twice_dist (z w : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.complexChordalDist (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ≤ 2 * dist z w := by
  have hz : 1 ≤ Real.sqrt (1 + ‖z‖ ^ 2) := Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖z‖])
  have hw : 1 ≤ Real.sqrt (1 + ‖w‖ ^ 2) := Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖w‖])
  have hp : 1 ≤ Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) (sub_nonneg.mpr hw)]
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.complexChordalDist_coe_coe, dist_eq_norm]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hp)).mpr
  nlinarith [norm_nonneg (z - w)]

/-- None of the actual parabolic cusp orbit points is in an original discontinuity domain. -/
theorem stableCusp_orbit_infty_not_mem (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : MobiusInvariantDomain G) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G
      D.carrier)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G) (g : G) : g.val.val ∞ ∉ D.carrier := by
  intro hg
  have hi : (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ D.carrier := by
    have hh := D.invariant g⁻¹ _ hg
    change g⁻¹ • (g • (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ∈ D.carrier at hh
    simpa only [inv_smul_smul] using hh
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.not_discontinuous_on_set_containing_parabolic_or_loxodromic_fixedPoint G D.carrier ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1, hT⟩
    (Or.inl ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff 1).mpr
      one_ne_zero)) ∞ hi
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1) hD

/-- The pole of an actual group matrix is below a contained normalized cusp. -/
theorem stableCusp_matrix_pole_below (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : MobiusInvariantDomain G) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G
      D.carrier)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G) (h : ℝ)
    (hQ : ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {z : ℂ | h < z.im} ⊆ D.carrier)
    (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B ∈ G) (hc : B 1 0 ≠ 0) :
    (-(B 1 1) / B 1 0).im ≤ h := by
  have hi : (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∉ D.carrier := by
    exact stableCusp_orbit_infty_not_mem G D hD hT (1 : G)
  have hp : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B).val
      ((-(B 1 1) / B 1 0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ∞ := by
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,
      _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_coe]
    change (if B 1 0 * (-(B 1 1) / B 1 0) + B 1 1 = 0 then ∞ else _) = ∞
    exact ite_eq_left ((_root_.LowDimensionalTopology.Geometry.Mobius.denominator_eq_zero_iff _ _ _ hc).mpr rfl)
  by_contra! hz
  have hm := D.invariant (⟨_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B, hB⟩ : G)
    ((-(B 1 1) / B 1 0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hQ ⟨_, hz, rfl⟩)
  exact hi (hp ▸ hm)

/-- Every genuine non-affine matrix image of a high cusp point is uniformly chordally
close to the corresponding actual ideal-point orbit. -/
theorem stableCusp_matrix_chordal (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) (h t :
  ℝ) (z : ℂ)
    (hc : 1 ≤ ‖B 1 0‖) (ht : h < t) (hz : t < z.im)
    (hpole : (-(B 1 1) / B 1 0).im ≤ h) :
    _root_.LowDimensionalTopology.Geometry.Mobius.complexChordalDist ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B).val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
      ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B).val ∞) < 2 / (t - h) := by
  obtain ⟨hd, hdist⟩ := stableCusp_matrix_distance B h t z hc ht hz hpole
  have hcn : B 1 0 ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hc)
  have hfin : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B).val (z :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
      (((B 0 0 * z + B 0 1) / (B 1 0 * z + B 1 1) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,
      _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_coe]
    exact ite_eq_right hd
  have hinfty : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B).val ∞ = ((B 0 0 / B 1 0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,
      _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_infty]
    exact ite_eq_right hcn
  rw [hfin, hinfty]
  have hh := lt_of_le_of_lt (stableCusp_chordal_le_twice_dist
    ((B 0 0 * z + B 0 1) / (B 1 0 * z + B 1 1)) (B 0 0 / B 1 0))
    (mul_lt_mul_of_pos_left hdist (by norm_num : (0 : ℝ) < 2))
  simpa only [div_eq_mul_inv] using hh

/-- A single height makes both affine and non-affine actual cusp images uniformly small. -/
theorem stableCusp_height_threshold (h ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, h < t ∧ 0 < t ∧ 2 / (t - h) < ε ∧ 2 / t < ε := by
  let t := max h 0 + (2 / ε + 1)
  have hdiv : 0 < 2 / ε := div_pos (by norm_num) hε
  have hm : h ≤ max h 0 := le_max_left _ _
  have hm0 : 0 ≤ max h 0 := le_max_right _ _
  have ht : h < t := by dsimp [t]; linarith
  have ht0 : 0 < t := by dsimp [t]; linarith
  have he : ε * (2 / ε) = 2 := mul_div_cancel₀ _ hε.ne'
  refine ⟨t, ht, ht0, (div_lt_iff₀ (sub_pos.mpr ht)).mpr ?_, (div_lt_iff₀ ht0).mpr ?_⟩
  · have hx := mul_nonneg hε.le (sub_nonneg.mpr hm)
    dsimp [t]
    nlinarith
  · have hx := mul_nonneg hε.le hm0
    dsimp [t]
    nlinarith

/-- All actual group images of a sufficiently high cusp stay uniformly chordally
close to their corresponding ideal-point orbit. The repaired full cusp stabilizer
condition is used exactly in the affine case. -/
theorem stableCusp_group_images_near_cusps (G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : MobiusInvariantDomain G) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G
      D.carrier)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G) (h : ℝ)
    (hQ : ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {z : ℂ | h < z.im} ⊆ D.carrier)
    (hfix : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ stableTranslationGroup)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, h < t ∧ ∀ f ∈ G, ∀ z : ℂ, t < z.im →
      _root_.LowDimensionalTopology.Geometry.Mobius.complexChordalDist (f.val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) (f.val ∞) < ε := by
  obtain ⟨t, ht, ht0, hε₁, hε₂⟩ := stableCusp_height_threshold h ε hε
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_invariant_discrete G D.carrier D.invariant D.isConnected.nonempty hD
  refine ⟨t, ht, ?_⟩
  intro f hf z hz
  obtain ⟨B, hB⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection_surjective f
  by_cases hc : B 1 0 = 0
  · have hfinfty : f.val ∞ = ∞ := by
      rw [← hB, _root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,
        _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_infty]
      exact ite_eq_left hc
    obtain ⟨n, hn⟩ := (stableTranslationGroup_mem f).mp (hfix f hf hfinfty)
    rw [hn, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty,
      _root_.LowDimensionalTopology.Geometry.Mobius.complexChordalDist_coe_infty]
    have hzim : t < (z + (n : ℂ)).im := by
      simpa only [Complex.add_im, Complex.intCast_im, add_zero] using hz
    have hznorm : (z + (n : ℂ)).im ≤ ‖z + (n : ℂ)‖ :=
      le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
    have hnormroot : ‖z + (n : ℂ)‖ ≤ Real.sqrt (1 + ‖z + (n : ℂ)‖ ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith)
    exact lt_trans (div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2) ht0
      (lt_of_lt_of_le hzim (hznorm.trans hnormroot))) hε₂
  · have hBG : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B ∈ G := hB.symm ▸ hf
    have hcn := stableCuspShimizu_lowerLeft G hd hT B hBG hc
    have hp := stableCusp_matrix_pole_below G D hD hT h hQ B hBG hc
    have hnear := stableCusp_matrix_chordal B h t z hcn ht hz hp
    rw [hB] at hnear
    exact hnear.trans hε₁

/-- Every compact subset of the original domain avoids all full-group translates of
one sufficiently high cusp tail. This is the genuine global end-separation estimate
needed to fill the cusp in the quotient. -/
theorem stableCusp_compact_tail_escape (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : MobiusInvariantDomain G) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G
      D.carrier)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G) (h : ℝ)
    (hQ : ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {z : ℂ | h < z.im} ⊆ D.carrier)
    (hfix : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ stableTranslationGroup)
    (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hK : IsCompact K) (hKD : K ⊆ D.carrier) :
    ∃ t : ℝ, h < t ∧ ∀ f ∈ G,
      Disjoint (f.val '' (((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {z : ℂ | t < z.im})) K := by
  obtain ⟨ε, hε, hsep⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.compact_open_chordal_separation D.isOpen hK hKD
  obtain ⟨t, ht, hnear⟩ := stableCusp_group_images_near_cusps G D hD hT h hQ hfix ε hε
  refine ⟨t, ht, ?_⟩
  intro f hf
  apply Set.disjoint_left.mpr
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩ hpK
  have hlo := hsep _ hpK (f.val ∞) (stableCusp_orbit_infty_not_mem G D hD hT ⟨f, hf⟩)
  exact (not_lt_of_ge hlo) (hnear f hf z hz)

end LowDimensionalTopology.Geometry.Surfaces
