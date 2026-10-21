module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Surfaces.Quotient.Mobius
public import LowDimensionalTopology.Geometry.Euclidean.Lattice
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteTranslationGroups
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import LowDimensionalTopology.Geometry.Surfaces.Covering.DiscUniversalDeck
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
noncomputable section
open scoped Topology OnePoint
open Set Filter Module
namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces

/-- For a discontinuous no-elliptic action, every actual fixed point in the domain has trivial stabilizer. -/
theorem mobius_noElliptic_fixed_eq_one {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {S : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H S)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (g : H) (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hz : z ∈ S) (hfix : g • z = z) : g = 1 := by
  exact mobius_noElliptic_finite_order_eq_one H hno g
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isOfFinOrder_of_finite_stabilizer g z (hD.finite_stabilizer z
      hz) hfix)

/--
The sphere-covering case: a discontinuous no-elliptic actual Mobius group on
the whole sphere is trivial.
-/
theorem mobius_sphere_discontinuous_noElliptic_eq_bot (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H Set.univ)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) : H = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 1
  by_contra hne
  obtain ⟨z, hz⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_has_boundary_fixed f hne
  have he := mobius_noElliptic_fixed_eq_one hD hno (⟨f, hf⟩ : H) z (Set.mem_univ z) hz
  exact hne (congrArg Subtype.val he)

/-- Invariance of the actual finite plane under the whole group forces infinity to be fixed. -/
theorem mobius_plane_invariant_fix_infty (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hInv : ∀ (g : H) (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), z ≠ ∞ → g • z ≠ ∞) (g : H) : g.val.val ∞ = ∞ := by
  by_contra hne
  have hh := hInv g⁻¹ (g • ∞) hne
  apply hh
  exact inv_smul_smul g ∞

/-- Every element in a discontinuous no-elliptic actual plane action is a genuine translation. -/
theorem mobius_plane_discontinuous_noElliptic_translations (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hInv : ∀ (g : H) (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), z ≠ ∞ → g • z ≠ ∞)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H (Set.range ((↑) : ℂ →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)))
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) (g : H) :
    ∃ b : ℂ, g.val = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b := by
  let a : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer := ⟨g.val,
    mobius_plane_invariant_fix_infty H hInv g⟩
  apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusMultiplier_eq_one_iff_translation a).mp
  by_contra hmul
  have hmul' : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusMultiplier a : ℂ) ≠ 1 := fun he => hmul (Units.ext
    he)
  have hd : 1 - (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusMultiplier a : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm
    hmul')
  let w : ℂ := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusAffineConstant a / (1 -
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusMultiplier a : ℂ))
  have hfix : g • (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    change a.val.val (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobius_affine_formula]
    congr 1
    dsimp [w]
    field_simp [hd]
    ring
  have hg : g = 1 := mobius_noElliptic_fixed_eq_one hD hno g (w :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ⟨w, rfl⟩ hfix
  have ha : a = 1 := Subtype.ext (congrArg (fun k : H => k.val) hg)
  exact hmul (by rw [ha]; exact _root_.LowDimensionalTopology.Geometry.Mobius.mobius_affine_parameters_one.1)


/-- The genuine finite plane as an invariant domain for any translation-only actual Mobius group. -/
def translationPlaneDomain (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
      b) : MobiusInvariantDomain H where
  carrier := Set.range ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  isOpen := OnePoint.isOpen_range_coe
  isConnected := isConnected_range OnePoint.continuous_coe
  invariant := by
    rintro g _ ⟨z, rfl⟩
    obtain ⟨b, hb⟩ := hT g.val g.property
    change g.val.val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ Set.range ((↑) : ℂ →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [hb, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
    exact ⟨z + b, rfl⟩

/-- The ordinary complex coordinate is a homeomorphism onto the actual finite-plane domain. -/
def translationPlaneHomeomorph (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b) :
    ℂ ≃ₜ (translationPlaneDomain H hT).carrier :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph

theorem translationPlaneHomeomorph_apply (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b) (z : ℂ) :
    (translationPlaneHomeomorph H hT z).val = (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := rfl

/-- The original actual Mobius orbit relation is exactly translation by the displacement subgroup. -/
theorem translationPlane_orbitRel_iff (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b) (z w : ℂ) :
    MulAction.orbitRel H (translationPlaneDomain H hT).carrier
      (translationPlaneHomeomorph H hT z) (translationPlaneHomeomorph H hT w) ↔
        z - w ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨b, hb⟩ := hT g.val g.property
    have hbH : b ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H := by
      change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b ∈ H
      rw [← hb]
      exact g.property
    have hval := congrArg Subtype.val hg
    change g.val.val (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hval
    rw [hb, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe] at hval
    have hc : w + b = z := OnePoint.coe_injective hval
    have hd : z - w = b := by rw [← hc]; ring
    exact hd.symm ▸ hbH
  · intro h
    refine ⟨⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (z - w), h⟩, ?_⟩
    apply Subtype.ext
    change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (z - w)).val (w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
    congr 1
    ring

/-- The actual plane orbit quotient has exactly the additive quotient topology. -/
def translationPlaneQuotientHomeomorph (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b) :
    MobiusDomainQuotient (translationPlaneDomain H hT) ≃ₜ ℂ ⧸ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H := by
  apply Homeomorph.Quotient.congr (translationPlaneHomeomorph H hT).symm
  intro x y
  obtain ⟨z, rfl⟩ := (translationPlaneHomeomorph H hT).surjective x
  obtain ⟨w, rfl⟩ := (translationPlaneHomeomorph H hT).surjective y
  rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
  rw [translationPlane_orbitRel_iff, QuotientAddGroup.leftRel_apply]
  change z - w ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H ↔ -z + w ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H
  have he : -z + w = -(z - w) := by ring
  rw [he]
  exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H).neg_mem_iff.symm


/-- The actual exponential coordinate for quotienting the plane by one nonzero period. -/
def complexPeriodExponential (b : ℂ) : C(ℂ, {z : ℂ // z ≠ 0}) where
  toFun z := ⟨Complex.exp ((2 * Real.pi * Complex.I / b) * z), Complex.exp_ne_zero _⟩
  continuous_toFun := Continuous.subtype_mk
    (Complex.continuous_exp.comp (continuous_const.mul continuous_id)) _

theorem complexPeriodExponential_isQuotientMap (b : ℂ) (hb : b ≠ 0) :
    Topology.IsQuotientMap (complexPeriodExponential b) := by
  have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  change Topology.IsQuotientMap ((fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘
    Homeomorph.mulLeft₀ (2 * Real.pi * Complex.I / b) (div_ne_zero hp hb))
  exact Complex.isAddQuotientCoveringMap_exp.toIsQuotientMap.comp
    (Homeomorph.mulLeft₀ _ (div_ne_zero hp hb)).isQuotientMap

/-- Exponential fibers are exactly the actual integer multiples of the original period. -/
theorem complexPeriodExponential_fiber_iff (b : ℂ) (hb : b ≠ 0) (z w : ℂ) :
    complexPeriodExponential b z = complexPeriodExponential b w ↔
      z - w ∈ AddSubgroup.zmultiples b := by
  rw [Subtype.ext_iff]
  change Complex.exp ((2 * Real.pi * Complex.I / b) * z) =
    Complex.exp ((2 * Real.pi * Complex.I / b) * w) ↔ _
  rw [Complex.exp_eq_exp_iff_exists_int, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [zsmul_eq_mul]
    field_simp [hb] at hn
    linear_combination -hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [zsmul_eq_mul] at hn
    field_simp [hb]
    linear_combination -hn

/-- The rank-one additive quotient is homeomorphic to the genuine punctured complex plane,
with its ordinary topology and the actual exponential formula. -/
def complexCyclicQuotientHomeomorph (b : ℂ) (hb : b ≠ 0) :
    (ℂ ⧸ AddSubgroup.zmultiples b) ≃ₜ {z : ℂ // z ≠ 0} := by
  refine (Homeomorph.Quotient.congrRight (r := QuotientAddGroup.leftRel (AddSubgroup.zmultiples b))
    (r' := Setoid.ker (complexPeriodExponential b)) ?_).trans
      (complexPeriodExponential_isQuotientMap b hb).homeomorph
  intro z w
  rw [QuotientAddGroup.leftRel_apply]
  change -z + w ∈ AddSubgroup.zmultiples b ↔ complexPeriodExponential b z = complexPeriodExponential b w
  rw [complexPeriodExponential_fiber_iff b hb]
  have he : -z + w = -(z - w) := by ring
  rw [he]
  exact (AddSubgroup.zmultiples b).neg_mem_iff


/-- A genuine global complex coordinate defines the ordinary one-chart complex atlas. -/
def globalChartRiemannAtlas {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (he : e.source = Set.univ) : RiemannAtlas X where
  charts := {e}
  cover x := ⟨e, rfl, he.symm ▸ Set.mem_univ x⟩
  compatible := by
    intro f hf g hg
    have hf' : f = e := hf
    have hg' : g = e := hg
    subst f
    subst g
    exact openPartialHomeomorph_self_transition_analytic e

/-- The one-chart surface uses the original Hausdorff connected topology. -/
def globalChartRiemannSurface {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    (e : OpenPartialHomeomorph X ℂ) (he : e.source = Set.univ) : RiemannSurface X where
  toRiemannAtlas := globalChartRiemannAtlas e he
  t2Space := inferInstance
  connectedSpace := inferInstance

/-- Analyticity in two genuine global coordinates is exactly the required actual chart expression. -/
theorem RiemannAnalyticMap.globalChart_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X ℂ) (he : e.source = Set.univ)
    (f : OpenPartialHomeomorph Y ℂ) (hf : f.source = Set.univ) (g : X → Y) :
    RiemannAnalyticMap (globalChartRiemannAtlas e he) (globalChartRiemannAtlas f hf) g ↔
      Continuous g ∧ AnalyticOnNhd ℂ (riemannChartMap e g f) (riemannChartMapDomain e g f) := by
  constructor
  · intro h
    exact ⟨h.1, h.2 e rfl f rfl⟩
  · rintro ⟨hc, ha⟩
    refine ⟨hc, ?_⟩
    intro e' he' f' hf'
    have hee : e' = e := he'
    have hff : f' = f := hf'
    subst e'
    subst f'
    exact ha

/-- The ordinary complex plane with its identity complex coordinate. -/
def complexPlaneRiemannSurface : RiemannSurface ℂ :=
  globalChartRiemannSurface (OpenPartialHomeomorph.refl ℂ) rfl

/-- The punctured plane uses its genuine open subset coordinate. -/
def puncturedPlaneChart : OpenPartialHomeomorph {z : ℂ // z ≠ 0} ℂ :=
  (⟨{z : ℂ | z ≠ 0}, isOpen_ne⟩ : TopologicalSpace.Opens ℂ).openPartialHomeomorphSubtypeCoe
    ⟨1, one_ne_zero⟩

theorem puncturedPlaneChart_source : puncturedPlaneChart.source = Set.univ := rfl

theorem puncturedPlaneChart_target : puncturedPlaneChart.target = {z : ℂ | z ≠ 0} := by
  simp [puncturedPlaneChart]

theorem puncturedPlaneChart_apply (z : {z : ℂ // z ≠ 0}) : puncturedPlaneChart z = z.val := rfl

/-- The standard punctured-plane Riemann surface, with its original connected topology. -/
def puncturedPlaneRiemannSurface : RiemannSurface {z : ℂ // z ≠ 0} := by
  let := Complex.isAddQuotientCoveringMap_exp.surjective.connectedSpace
    Complex.isAddQuotientCoveringMap_exp.continuous
  exact globalChartRiemannSurface puncturedPlaneChart puncturedPlaneChart_source

/-- The actual scaled exponential projection is analytic between the standard complex surfaces. -/
theorem complexPeriodExponential_analytic (b : ℂ) :
    RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas
      puncturedPlaneRiemannSurface.toRiemannAtlas (complexPeriodExponential b) := by
  apply (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.globalChart_iff (OpenPartialHomeomorph.refl
    ℂ) rfl
    puncturedPlaneChart puncturedPlaneChart_source (complexPeriodExponential b)).mpr
  refine ⟨(complexPeriodExponential b).continuous, ?_⟩
  change AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp ((2 * Real.pi * Complex.I / b) * z)) _
  intro z _hz
  exact (analyticAt_const.mul analyticAt_id).cexp


/-- Membership in a real basis's integer lattice is exactly integrality of all real coordinates. -/
theorem complexIntegerSpan_mem_iff_coordinates (b : Basis (Fin 2) ℝ ℂ) (z : ℂ) :
    z ∈ Submodule.span ℤ (Set.range b) ↔ ∀ i, ∃ n : ℤ, b.equivFun z i = n := by
  constructor
  · intro hz
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hz
    have hreal : ∑ i, (c i : ℝ) • b i = z := by simpa only [Int.cast_smul_eq_zsmul] using hc
    have hr := congrArg b.equivFun hreal
    rw [← b.equivFun_symm_apply, b.equivFun.apply_symm_apply] at hr
    intro i
    exact ⟨c i, (congrFun hr i).symm⟩
  · intro hz
    choose c hc using hz
    apply (Submodule.mem_span_range_iff_exists_fun ℤ).mpr
    refine ⟨c, ?_⟩
    have he : ∑ i, (c i : ℝ) • b i = z := by
      apply b.equivFun.injective
      rw [← b.equivFun_symm_apply, b.equivFun.apply_symm_apply]
      funext i
      exact (hc i).symm
    simpa only [Int.cast_smul_eq_zsmul] using he

/-- Taking the two real coordinates modulo integers is the genuine topological torus projection. -/
def complexLatticeTorusMap (b : Basis (Fin 2) ℝ ℂ) : C(ℂ, Fin 2 → AddCircle (1 : ℝ)) where
  toFun z i := (b.equivFun z i : AddCircle (1 : ℝ))
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact QuotientAddGroup.continuous_mk.comp ((continuous_apply i).comp b.equivFunL.continuous)

theorem complexLatticeTorusMap_isQuotientMap (b : Basis (Fin 2) ℝ ℂ) :
    Topology.IsQuotientMap (complexLatticeTorusMap b) := by
  have hq := IsOpenQuotientMap.piMap
    (fun _i : Fin 2 => QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1 : ℝ)))
  exact hq.isQuotientMap.comp b.equivFunL.toHomeomorph.isQuotientMap

/-- Equal torus coordinates identify exactly the points differing by an integer lattice vector. -/
theorem complexLatticeTorusMap_fiber_iff (b : Basis (Fin 2) ℝ ℂ) (z w : ℂ) :
    complexLatticeTorusMap b z = complexLatticeTorusMap b w ↔
      z - w ∈ Submodule.span ℤ (Set.range b) := by
  rw [complexIntegerSpan_mem_iff_coordinates]
  change (fun i => (b.equivFun z i : AddCircle (1 : ℝ))) =
    (fun i => (b.equivFun w i : AddCircle (1 : ℝ))) ↔ _
  rw [funext_iff]
  apply forall_congr'
  intro i
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  simp only [map_sub, Pi.sub_apply, zsmul_eq_mul, mul_one]
  exact exists_congr (fun n => eq_comm)

/-- The rank-two complex lattice quotient is homeomorphic to the actual product of two circles. -/
def complexLatticeQuotientTorusHomeomorph (b : Basis (Fin 2) ℝ ℂ) :
    (ℂ ⧸ (Submodule.span ℤ (Set.range b)).toAddSubgroup) ≃ₜ
      AddCircle (1 : ℝ) × AddCircle (1 : ℝ) := by
  let e : (ℂ ⧸ (Submodule.span ℤ (Set.range b)).toAddSubgroup) ≃ₜ
      Quotient (Setoid.ker (complexLatticeTorusMap b)) :=
    Homeomorph.Quotient.congrRight (by
      intro z w
      rw [QuotientAddGroup.leftRel_apply]
      change -z + w ∈ Submodule.span ℤ (Set.range b) ↔ complexLatticeTorusMap b z = complexLatticeTorusMap b w
      rw [complexLatticeTorusMap_fiber_iff]
      have he : -z + w = -(z - w) := by ring
      rw [he]
      exact (Submodule.span ℤ (Set.range b)).neg_mem_iff)
  exact e.trans ((complexLatticeTorusMap_isQuotientMap b).homeomorph.trans (Homeomorph.finTwoArrow))


/-- The ordinary plane embeds analytically into the actual two-chart Riemann sphere. -/
theorem complexPlane_coe_analytic :
    RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas sphereRiemannSurface.toRiemannAtlas
      ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  refine ⟨OnePoint.continuous_coe, ?_⟩
  intro e he g hg
  have hee : e = OpenPartialHomeomorph.refl ℂ := he
  subst e
  change g ∈ sphereCharts at hg
  simp only [sphereCharts, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · intro z _hz
    change AnalyticAt ℂ (fun w : ℂ => sphereFiniteChart (w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) z
    convert (analyticAt_id (𝕜 := ℂ) (z := z)) using 1
    funext w
    exact sphereFiniteChart_coe w
  · intro z hz
    have hzsource : (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ sphereInfinityChart.source := hz.2
    rw [sphereInfinityChart_source] at hzsource
    have hz0 : z ≠ 0 := by
      intro hez
      apply hzsource
      exact congrArg (fun w : ℂ => (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) hez
    change AnalyticAt ℂ (fun w : ℂ => sphereInfinityChart (w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) z
    apply (analyticAt_id.inv hz0).congr
    filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
    exact (sphereInfinityChart_coe w hw).symm

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces

/-- The ordinary plane coordinate is analytic in the genuine inherited sphere-domain atlas. -/
theorem translationPlaneHomeomorph_analytic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b) :
    RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas
      (mobiusDomainRiemannSurface (translationPlaneDomain H hT)).toRiemannAtlas
      (translationPlaneHomeomorph H hT) := by
  let D := translationPlaneDomain H hT
  have hi : RiemannAnalyticMap (mobiusDomainRiemannSurface D).toRiemannAtlas sphereRiemannAtlas
      (Subtype.val : D.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :=
    sphereRiemannAtlas.liftLocalHomeomorph_projection_analytic _
      D.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_localHomeomorph hi
    D.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph (translationPlaneHomeomorph H hT).continuous
  exact complexPlane_coe_analytic

/-- The actual finite-plane orbit projection expressed in its original complex coordinate. -/
def translationPlaneProjection (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b) :
    ℂ → MobiusDomainQuotient (translationPlaneDomain H hT) :=
  mobiusDomainProjection (translationPlaneDomain H hT) ∘ translationPlaneHomeomorph H hT

theorem translationPlaneProjection_surjective (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b) :
    Function.Surjective (translationPlaneProjection H hT) :=
  (mobiusDomainProjection_surjective _).comp (translationPlaneHomeomorph H hT).surjective

theorem translationPlaneProjection_analytic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H (translationPlaneDomain H
      hT).carrier) :
    RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas
      (mobiusQuotientRiemannSurface (translationPlaneDomain H hT) hD).toRiemannAtlas
      (translationPlaneProjection H hT) :=
  (mobiusDomainProjection_analytic _ hD).comp (translationPlaneHomeomorph_analytic H hT)

theorem translationPlaneProjection_covering (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H (translationPlaneDomain H
      hT).carrier)
    (hno : ∀ g ∈ H, g ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    IsCoveringMap (translationPlaneProjection H hT) :=
  (mobiusDomain_noElliptic_covering _ hD hno).isCoveringMap.comp_homeomorph
    (translationPlaneHomeomorph H hT)

theorem translationPlaneQuotientHomeomorph_apply_mk (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b) (z : ℂ) :
    translationPlaneQuotientHomeomorph H hT (translationPlaneProjection H hT z) =
      (QuotientAddGroup.mk z : ℂ ⧸ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H) := by
  change Quotient.mk _ ((translationPlaneHomeomorph H hT).symm (translationPlaneHomeomorph H hT z)) = _
  rw [Homeomorph.symm_apply_apply]

/-- Equality of actual displacement subgroups induces the identity-coordinate quotient homeomorphism. -/
def complexAddQuotientCongr (L M : AddSubgroup ℂ) (h : L = M) : (ℂ ⧸ L) ≃ₜ ℂ ⧸ M :=
  Homeomorph.Quotient.congrRight (by intro z w; rw [h])

theorem complexAddQuotientCongr_apply_mk (L M : AddSubgroup ℂ) (h : L = M) (z : ℂ) :
    complexAddQuotientCongr L M h (QuotientAddGroup.mk z) = QuotientAddGroup.mk z := rfl

theorem complexCyclicQuotientHomeomorph_apply_mk (b : ℂ) (hb : b ≠ 0) (z : ℂ) :
    complexCyclicQuotientHomeomorph b hb (QuotientAddGroup.mk z) = complexPeriodExponential b z := rfl

/-- The rank-one actual Mobius plane quotient is conformally the standard punctured plane,
for the original branched quotient atlas and the genuine exponential coordinate. -/
theorem translationPlaneQuotient_cyclic_conformallyEquivalent (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H (translationPlaneDomain H
      hT).carrier)
    (hno : ∀ g ∈ H, g ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (b : ℂ) (hb : b ≠ 0) (hL : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H =
      AddSubgroup.zmultiples b) :
    RiemannConformallyEquivalent (mobiusQuotientRiemannSurface (translationPlaneDomain H hT) hD)
      puncturedPlaneRiemannSurface := by
  let eL := complexAddQuotientCongr (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements
    H) (AddSubgroup.zmultiples b) hL
  let E := (translationPlaneQuotientHomeomorph H hT).trans (eL.trans (complexCyclicQuotientHomeomorph b hb))
  have hcomp : (E : MobiusDomainQuotient (translationPlaneDomain H hT) → {z : ℂ // z ≠ 0}) ∘
      translationPlaneProjection H hT = complexPeriodExponential b := by
    funext z
    change complexCyclicQuotientHomeomorph b hb
      (eL (translationPlaneQuotientHomeomorph H hT (translationPlaneProjection H hT z))) = _
    rw [translationPlaneQuotientHomeomorph_apply_mk, complexAddQuotientCongr_apply_mk,
      complexCyclicQuotientHomeomorph_apply_mk]
  refine ⟨E, ?_, E.bijective⟩
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_surjective_localHomeomorph
    (translationPlaneProjection_analytic H hT hD)
    (translationPlaneProjection_covering H hT hD hno).isLocalHomeomorph
    (translationPlaneProjection_surjective H hT) E.continuous
  rw [hcomp]
  exact complexPeriodExponential_analytic b

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces

/-- The zero-period quotient is the ordinary complex plane, with its original topology. -/
def complexZeroQuotientHomeomorph : (ℂ ⧸ (⊥ : AddSubgroup ℂ)) ≃ₜ ℂ := by
  refine (Homeomorph.Quotient.congrRight (r := QuotientAddGroup.leftRel (⊥ : AddSubgroup ℂ))
    (r' := (⊥ : Setoid ℂ)) ?_).trans Homeomorph.quotientBot
  intro z w
  rw [QuotientAddGroup.leftRel_apply]
  change -z + w = 0 ↔ z = w
  constructor
  · intro h
    linear_combination -h
  · rintro rfl
    simp

theorem complexZeroQuotientHomeomorph_apply_mk (z : ℂ) :
    complexZeroQuotientHomeomorph (QuotientAddGroup.mk z) = z := rfl

/-- The rank-zero actual plane quotient is conformally the standard complex plane,
with the original quotient complex atlas. -/
theorem translationPlaneQuotient_zero_conformallyEquivalent (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H (translationPlaneDomain H
      hT).carrier)
    (hno : ∀ g ∈ H, g ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (hL : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H = ⊥) :
    RiemannConformallyEquivalent (mobiusQuotientRiemannSurface (translationPlaneDomain H hT) hD)
      complexPlaneRiemannSurface := by
  let eL := complexAddQuotientCongr (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements
    H) ⊥ hL
  let E := (translationPlaneQuotientHomeomorph H hT).trans (eL.trans complexZeroQuotientHomeomorph)
  have hcomp : (E : MobiusDomainQuotient (translationPlaneDomain H hT) → ℂ) ∘
      translationPlaneProjection H hT = id := by
    funext z
    change complexZeroQuotientHomeomorph
      (eL (translationPlaneQuotientHomeomorph H hT (translationPlaneProjection H hT z))) = z
    rw [translationPlaneQuotientHomeomorph_apply_mk, complexAddQuotientCongr_apply_mk,
      complexZeroQuotientHomeomorph_apply_mk]
  refine ⟨E, ?_, E.bijective⟩
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_surjective_localHomeomorph
    (translationPlaneProjection_analytic H hT hD)
    (translationPlaneProjection_covering H hT hD hno).isLocalHomeomorph
    (translationPlaneProjection_surjective H hT) E.continuous
  rw [hcomp]
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.id complexPlaneRiemannSurface.toRiemannAtlas

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces Module

/-- The original finite-plane projection has exactly the displacement-lattice fibers. -/
theorem translationPlaneProjection_fiber_iff (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b) (z w : ℂ) :
    translationPlaneProjection H hT z = translationPlaneProjection H hT w ↔
      z - w ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H := by
  constructor
  · intro h
    exact (translationPlane_orbitRel_iff H hT z w).mp (Quotient.exact h)
  · intro h
    exact Quotient.sound ((translationPlane_orbitRel_iff H hT z w).mpr h)

/-- The standard topological torus has its actual product-of-circles topology. -/
abbrev ComplexTorusCarrier := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- A flat complex torus model has a genuine analytic covering from the complex plane
with precisely the integer lattice of the specified real basis as its fibers. -/
structure ComplexTorusModel (b : Basis (Fin 2) ℝ ℂ) where
  surface : RiemannSurface ComplexTorusCarrier
  projection : ℂ → ComplexTorusCarrier
  covering : IsCoveringMap projection
  surjective : Function.Surjective projection
  analytic_projection : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas
    surface.toRiemannAtlas projection
  fiber_iff : ∀ z w, projection z = projection w ↔ z - w ∈ Submodule.span ℤ (Set.range b)

/-- A real-basis displacement lattice identifies the actual orbit quotient with the genuine torus. -/
def translationPlaneQuotientTorusHomeomorph (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ a : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation a) (b : Basis
      (Fin 2) ℝ ℂ)
    (hL : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H = (Submodule.span ℤ
      (Set.range b)).toAddSubgroup) :
    MobiusDomainQuotient (translationPlaneDomain H hT) ≃ₜ ComplexTorusCarrier :=
  (translationPlaneQuotientHomeomorph H hT).trans
    ((complexAddQuotientCongr _ _ hL).trans (complexLatticeQuotientTorusHomeomorph b))

/-- The original complex quotient charts give a complex structure on the actual torus carrier. -/
def translationTorusRiemannSurface (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ a : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation a)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H (translationPlaneDomain H
      hT).carrier)
    (b : Basis (Fin 2) ℝ ℂ)
    (hL : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H = (Submodule.span ℤ
      (Set.range b)).toAddSubgroup) :
    RiemannSurface ComplexTorusCarrier where
  toRiemannAtlas := (mobiusQuotientRiemannSurface (translationPlaneDomain H hT) hD).toRiemannAtlas.liftLocalHomeomorph
    (translationPlaneQuotientTorusHomeomorph H hT b hL).symm
    (translationPlaneQuotientTorusHomeomorph H hT b hL).symm.isLocalHomeomorph
  t2Space := inferInstance
  connectedSpace := inferInstance

theorem translationPlaneQuotientTorusHomeomorph_analytic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ a : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation a)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H (translationPlaneDomain H
      hT).carrier)
    (b : Basis (Fin 2) ℝ ℂ)
    (hL : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H = (Submodule.span ℤ
      (Set.range b)).toAddSubgroup) :
    RiemannAnalyticMap (mobiusQuotientRiemannSurface (translationPlaneDomain H hT) hD).toRiemannAtlas
      (translationTorusRiemannSurface H hT hD b hL).toRiemannAtlas
      (translationPlaneQuotientTorusHomeomorph H hT b hL) := by
  let E := translationPlaneQuotientTorusHomeomorph H hT b hL
  have hi : RiemannAnalyticMap (translationTorusRiemannSurface H hT hD b hL).toRiemannAtlas
      (mobiusQuotientRiemannSurface (translationPlaneDomain H hT) hD).toRiemannAtlas E.symm :=
    (mobiusQuotientRiemannSurface (translationPlaneDomain H hT)
      hD).toRiemannAtlas.liftLocalHomeomorph_projection_analytic
      E.symm E.symm.isLocalHomeomorph
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_localHomeomorph hi E.symm.isLocalHomeomorph E.continuous
  have he : (E.symm : ComplexTorusCarrier → _) ∘ E = id := by
    funext z
    exact E.symm_apply_apply z
  rw [he]
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.id _

/-- The actual rank-two quotient has a genuine flat complex-torus model, including
its analytic plane cover and the original integer lattice fibers. -/
def translationComplexTorusModel (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ a : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation a)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H (translationPlaneDomain H
      hT).carrier)
    (hno : ∀ g ∈ H, g ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (b : Basis (Fin 2) ℝ ℂ)
    (hL : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H = (Submodule.span ℤ
      (Set.range b)).toAddSubgroup) :
    ComplexTorusModel b where
  surface := translationTorusRiemannSurface H hT hD b hL
  projection := translationPlaneQuotientTorusHomeomorph H hT b hL ∘ translationPlaneProjection H hT
  covering := (translationPlaneProjection_covering H hT hD hno).homeomorph_comp
    (translationPlaneQuotientTorusHomeomorph H hT b hL)
  surjective := (translationPlaneQuotientTorusHomeomorph H hT b hL).surjective.comp
    (translationPlaneProjection_surjective H hT)
  analytic_projection := (translationPlaneQuotientTorusHomeomorph_analytic H hT hD b hL).comp
    (translationPlaneProjection_analytic H hT hD)
  fiber_iff := by
    intro z w
    rw [Function.comp_apply, Function.comp_apply,
      (translationPlaneQuotientTorusHomeomorph H hT b hL).injective.eq_iff,
      translationPlaneProjection_fiber_iff, hL]
    rfl

theorem translationPlaneQuotient_torus_conformallyEquivalent (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ a : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation a)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H (translationPlaneDomain H
      hT).carrier)
    (hno : ∀ g ∈ H, g ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (b : Basis (Fin 2) ℝ ℂ)
    (hL : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H = (Submodule.span ℤ
      (Set.range b)).toAddSubgroup) :
    RiemannConformallyEquivalent (mobiusQuotientRiemannSurface (translationPlaneDomain H hT) hD)
      (translationComplexTorusModel H hT hD hno b hL).surface :=
  ⟨translationPlaneQuotientTorusHomeomorph H hT b hL,
    translationPlaneQuotientTorusHomeomorph_analytic H hT hD b hL,
    (translationPlaneQuotientTorusHomeomorph H hT b hL).bijective⟩

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces Module

/-- Every discontinuous no-elliptic translation quotient of the genuine finite plane is
conformally a plane, a punctured plane, or a flat complex torus with a real-basis period lattice. -/
theorem translationPlaneQuotient_conformal_trichotomy (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ a : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation a)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H (translationPlaneDomain H
      hT).carrier)
    (hno : ∀ g ∈ H, g ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    RiemannConformallyEquivalent (mobiusQuotientRiemannSurface (translationPlaneDomain H hT) hD)
        complexPlaneRiemannSurface ∨
    RiemannConformallyEquivalent (mobiusQuotientRiemannSurface (translationPlaneDomain H hT) hD)
        puncturedPlaneRiemannSurface ∨
    ∃ b : Basis (Fin 2) ℝ ℂ, ∃ T : ComplexTorusModel b,
      RiemannConformallyEquivalent (mobiusQuotientRiemannSurface (translationPlaneDomain H hT) hD)
        T.surface := by
  let D := translationPlaneDomain H hT
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_invariant_discrete H D.carrier
    D.invariant D.isConnected.nonempty hD
  obtain ⟨n, hn, v, hv,
    hspan⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements_basis H hd
  interval_cases n
  · left
    apply translationPlaneQuotient_zero_conformallyEquivalent H hT hD hno
    apply SetLike.coe_injective
    rw [hspan, Set.range_eq_empty_iff.mpr (inferInstance : IsEmpty (Fin 0)), Submodule.span_empty]
    rfl
  · right
    left
    have hne : v 0 ≠ 0 := hv.ne_zero 0
    apply translationPlaneQuotient_cyclic_conformallyEquivalent H hT hD hno (v 0) hne
    ext z
    change z ∈ (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H : Set
      ℂ) ↔ z ∈ AddSubgroup.zmultiples (v 0)
    rw [hspan]
    change z ∈ Submodule.span ℤ (Set.range v) ↔ z ∈ AddSubgroup.zmultiples (v 0)
    rw [Submodule.mem_span_range_iff_exists_fun ℤ, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c 0, by simpa only [Fin.sum_univ_one] using hc⟩
    · rintro ⟨c, hc⟩
      exact ⟨fun _ => c, by simpa only [Fin.sum_univ_one] using hc⟩
  · right
    right
    have hcard : Fintype.card (Fin 2) = Module.finrank ℝ ℂ := by
      rw [Fintype.card_fin, Complex.finrank_real_complex]
    let b : Basis (Fin 2) ℝ ℂ := basisOfLinearIndependentOfCardEqFinrank hv hcard
    have hb : (b : Fin 2 → ℂ) = v := coe_basisOfLinearIndependentOfCardEqFinrank hv hcard
    have hL : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H = (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
      apply SetLike.coe_injective
      change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements H : Set
        ℂ) = (Submodule.span ℤ (Set.range b) : Set ℂ)
      rw [hb]
      exact hspan
    exact ⟨b, translationComplexTorusModel H hT hD hno b hL,
      translationPlaneQuotient_torus_conformallyEquivalent H hT hD hno b hL⟩

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces Module

/-- The original orbit quotient of a trivial group is homeomorphic to its genuine domain. -/
def mobiusTrivialQuotientHomeomorph (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hH
  : H = ⊥)
    (D : MobiusInvariantDomain H) : MobiusDomainQuotient D ≃ₜ D.carrier := by
  refine (Homeomorph.Quotient.congrRight (r := MulAction.orbitRel H D.carrier)
    (r' := (⊥ : Setoid D.carrier)) ?_).trans Homeomorph.quotientBot
  intro x y
  change (∃ g : H, g • y = x) ↔ x = y
  constructor
  · rintro ⟨g, hg⟩
    have hg1 : g = 1 := by
      apply Subtype.ext
      change g.val = (1 : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
      simpa only [hH, Subgroup.mem_bot] using g.property
    simpa only [hg1, one_smul] using hg.symm
  · rintro rfl
    exact ⟨1, one_smul _ _⟩

theorem mobiusTrivialQuotientHomeomorph_apply_mk (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hH : H = ⊥)
    (D : MobiusInvariantDomain H) (z : D.carrier) :
    mobiusTrivialQuotientHomeomorph H hH D (mobiusDomainProjection D z) = z := rfl

/-- The trivial-group quotient has exactly the original domain complex structure up to
an actual analytic bijection, using the original quotient atlas. -/
theorem mobius_trivialQuotient_conformallyEquivalent_domain (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : H = ⊥) (D : MobiusInvariantDomain H) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H D.carrier) :
    RiemannConformallyEquivalent (mobiusQuotientRiemannSurface D hD) (mobiusDomainRiemannSurface D) := by
  have hno : ∀ g ∈ H, g ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g := by
    intro g hg hn
    exact (hn (by simpa only [hH, Subgroup.mem_bot] using hg)).elim
  let E := mobiusTrivialQuotientHomeomorph H hH D
  have hcomp : (E : MobiusDomainQuotient D → D.carrier) ∘ mobiusDomainProjection D = id := by
    funext z
    exact mobiusTrivialQuotientHomeomorph_apply_mk H hH D z
  refine ⟨E, ?_, E.bijective⟩
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_surjective_localHomeomorph (mobiusDomainProjection_analytic D hD)
    (mobiusDomain_noElliptic_covering D hD hno).isCoveringMap.isLocalHomeomorph
    (mobiusDomainProjection_surjective D) E.continuous
  rw [hcomp]
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.id _

/-- The entire actual Riemann sphere is an invariant domain for every Mobius subgroup. -/
def sphereMobiusDomain (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : MobiusInvariantDomain H where
  carrier := Set.univ
  isOpen := isOpen_univ
  isConnected := isConnected_univ
  invariant := fun _ _ _ => Set.mem_univ _

def sphereDomainHomeomorph (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    (sphereMobiusDomain H).carrier ≃ₜ _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex where
  toFun := Subtype.val
  invFun z := ⟨z, Set.mem_univ z⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk continuous_id _

/-- The no-elliptic discontinuous quotient of the entire actual sphere is conformally
the standard Riemann sphere, rather than merely having trivial abstract group. -/
theorem mobius_sphere_quotient_conformallyEquivalent (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H (sphereMobiusDomain
      H).carrier)
    (hno : ∀ g ∈ H, g ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    RiemannConformallyEquivalent (mobiusQuotientRiemannSurface (sphereMobiusDomain H) hD)
      sphereRiemannSurface := by
  have hH : H = ⊥ := mobius_sphere_discontinuous_noElliptic_eq_bot H hD hno
  apply (mobius_trivialQuotient_conformallyEquivalent_domain H hH (sphereMobiusDomain H) hD).trans
  refine ⟨sphereDomainHomeomorph H, ?_, (sphereDomainHomeomorph H).bijective⟩
  exact sphereRiemannAtlas.liftLocalHomeomorph_projection_analytic _
    (sphereMobiusDomain H).isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph

/-- The original finite-plane invariance and discontinuity hypotheses suffice for the
three conformal quotient models; being a translation group is proved, not assumed. -/
theorem mobius_plane_quotient_conformal_classification (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hInv : ∀ (g : H) (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), z ≠ ∞ → g • z ≠ ∞)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H (Set.range ((↑) : ℂ →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)))
    (hno : ∀ g ∈ H, g ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    ∃ hT : ∀ g ∈ H, ∃ a : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation a,
      RiemannConformallyEquivalent (mobiusQuotientRiemannSurface (translationPlaneDomain H hT) hD)
          complexPlaneRiemannSurface ∨
      RiemannConformallyEquivalent (mobiusQuotientRiemannSurface (translationPlaneDomain H hT) hD)
          puncturedPlaneRiemannSurface ∨
      ∃ b : Basis (Fin 2) ℝ ℂ, ∃ T : ComplexTorusModel b,
        RiemannConformallyEquivalent (mobiusQuotientRiemannSurface (translationPlaneDomain H hT) hD)
          T.surface := by
  have hT : ∀ g ∈ H, ∃ a : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation a := by
    intro g hg
    exact mobius_plane_discontinuous_noElliptic_translations H hInv hD hno ⟨g, hg⟩
  exact ⟨hT, translationPlaneQuotient_conformal_trichotomy H hT hD hno⟩

end LowDimensionalTopology.Geometry.Surfaces
