module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Atlas
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Normed.Field.Lemmas
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteCyclicGroups
public import LowDimensionalTopology.Geometry.Surfaces.Covering.DiscUniversalDeck
public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.EuclideanQuotientSurfaces
@[expose] public section
noncomputable section
open Set Filter Topology
namespace LowDimensionalTopology.Geometry.Surfaces

/-- Reciprocal conjugation of a zero-preserving plane homeomorphism is continuous even at
zero, by properness at infinity. -/
theorem plane_reciprocal_conjugate_continuous (e : ℂ ≃ₜ ℂ) (he : e 0 = 0) :
    Continuous (fun z : ℂ => (e z⁻¹)⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    rw [continuousAt_iff_punctured_nhds]
    simp only [inv_zero, he]
    have h₁ : Tendsto (Inv.inv : ℂ → ℂ) (𝓝[≠] 0) (cocompact ℂ) := by
      simpa only [Metric.cobounded_eq_cocompact] using
        (Filter.tendsto_inv₀_nhdsNE_zero (α := ℂ))
    have h₂ : Tendsto (Inv.inv : ℂ → ℂ) (cocompact ℂ) (𝓝 0) := by
      simpa only [Metric.cobounded_eq_cocompact] using
        (Filter.tendsto_inv₀_cobounded (α := ℂ))
    have heproper : Tendsto e (cocompact ℂ) (cocompact ℂ) := e.map_cocompact.le
    exact h₂.comp (heproper.comp h₁)
  · have hez : e z⁻¹ ≠ 0 := by
      intro hh
      have hh' : z⁻¹ = 0 := e.injective (hh.trans he.symm)
      exact hz (inv_eq_zero.mp hh')
    exact (e.continuous.continuousAt.comp (continuousAt_inv₀ hz)).inv₀ hez

/-- The reciprocal conjugate is a genuine whole-plane homeomorphism, including the
continuous extension across zero. -/
def planeReciprocalConjugateHomeomorph (e : ℂ ≃ₜ ℂ) (he : e 0 = 0) : ℂ ≃ₜ ℂ where
  toEquiv := (Equiv.inv ℂ).trans (e.toEquiv.trans (Equiv.inv ℂ))
  continuous_toFun := plane_reciprocal_conjugate_continuous e he
  continuous_invFun := plane_reciprocal_conjugate_continuous e.symm (by
    apply e.injective
    rw [e.apply_symm_apply, he])

theorem planeReciprocalConjugateHomeomorph_apply (e : ℂ ≃ₜ ℂ) (he : e 0 = 0) (z : ℂ) :
    planeReciprocalConjugateHomeomorph e he z = (e z⁻¹)⁻¹ := rfl

theorem planeReciprocalConjugateHomeomorph_zero (e : ℂ ≃ₜ ℂ) (he : e 0 = 0) :
    planeReciprocalConjugateHomeomorph e he 0 = 0 := by
  rw [planeReciprocalConjugateHomeomorph_apply, inv_zero, he, inv_zero]

/-- Reciprocal conjugation of an entire zero-preserving plane automorphism is entire;
properness supplies the removable value at zero. -/
theorem planeReciprocalConjugateHomeomorph_analytic (e : ℂ ≃ₜ ℂ) (he : e 0 = 0)
    (ha : AnalyticOnNhd ℂ e Set.univ) :
    AnalyticOnNhd ℂ (planeReciprocalConjugateHomeomorph e he) Set.univ := by
  have hpunct (z : ℂ) (hz : z ≠ 0) : AnalyticAt ℂ (planeReciprocalConjugateHomeomorph e he) z := by
    have hez : e z⁻¹ ≠ 0 := by
      intro hh
      exact hz (inv_eq_zero.mp (e.injective (hh.trans he.symm)))
    exact ((ha z⁻¹ (Set.mem_univ _)).comp (analyticAt_inv hz)).inv hez
  intro z _hz
  by_cases hz : z = 0
  · subst z
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ (planeReciprocalConjugateHomeomorph e he).continuous.continuousAt
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (hpunct w hw).differentiableAt
  · exact hpunct z hz

/-- Translating the image centers a plane automorphism at zero without changing its
whole-plane topology. -/
def planeCenteredHomeomorph (e : ℂ ≃ₜ ℂ) : ℂ ≃ₜ ℂ :=
  e.trans (Homeomorph.addRight (-(e 0)))

theorem planeCenteredHomeomorph_apply (e : ℂ ≃ₜ ℂ) (z : ℂ) :
    planeCenteredHomeomorph e z = e z - e 0 := rfl

theorem planeCenteredHomeomorph_zero (e : ℂ ≃ₜ ℂ) : planeCenteredHomeomorph e 0 = 0 := by
  simp [planeCenteredHomeomorph_apply]

theorem planeCenteredHomeomorph_analytic (e : ℂ ≃ₜ ℂ) (ha : AnalyticOnNhd ℂ e Set.univ) :
    AnalyticOnNhd ℂ (planeCenteredHomeomorph e) Set.univ := by
  intro z hz
  exact (ha z hz).sub analyticAt_const

/-- The entire divided difference of a plane automorphism has a finite limit at infinity,
obtained from its reciprocal conjugate's nonzero derivative at zero. -/
theorem plane_analytic_automorphism_dslope_tendsto (e : ℂ ≃ₜ ℂ)
    (ha : AnalyticOnNhd ℂ e Set.univ) :
    ∃ a : ℂ, a ≠ 0 ∧ Tendsto (dslope e 0) (cocompact ℂ) (𝓝 a) := by
  let h := planeCenteredHomeomorph e
  have hh : h 0 = 0 := planeCenteredHomeomorph_zero e
  let F := planeReciprocalConjugateHomeomorph h hh
  have hF : AnalyticOnNhd ℂ F Set.univ := planeReciprocalConjugateHomeomorph_analytic h hh
    (planeCenteredHomeomorph_analytic e ha)
  have hF0 : F 0 = 0 := planeReciprocalConjugateHomeomorph_zero h hh
  have hd : deriv F 0 ≠ 0 := openPartialHomeomorph_analytic_forward_deriv_ne_zero
    F.toOpenPartialHomeomorph hF 0 (Set.mem_univ _)
  have hs : ContinuousAt (dslope F 0) 0 := continuousAt_dslope_same.mpr
    (hF 0 (Set.mem_univ _)).differentiableAt
  have hinv : Tendsto (Inv.inv : ℂ → ℂ) (cocompact ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using
      (Filter.tendsto_inv₀_cobounded (α := ℂ))
  have hlim : Tendsto (fun z : ℂ => (dslope F 0 z⁻¹)⁻¹)
      (cocompact ℂ) (𝓝 (deriv F 0)⁻¹) := by
    have hds : Tendsto (fun z : ℂ => dslope F 0 z⁻¹) (cocompact ℂ) (𝓝 (deriv F 0)) := by
      convert hs.tendsto.comp hinv using 1
      · funext z
        rfl
      · rw [dslope_same]
    exact hds.inv₀ hd
  refine ⟨(deriv F 0)⁻¹, inv_ne_zero hd, hlim.congr' ?_⟩
  filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz
  have hz0 : z ≠ 0 := hz
  rw [dslope_of_ne e hz0, dslope_of_ne F (inv_ne_zero hz0), slope_def_field,
    slope_def_field, hF0, sub_zero, sub_zero, sub_zero]
  change (((e (z⁻¹)⁻¹ - e 0)⁻¹ / z⁻¹)⁻¹) = (e z - e 0) / z
  rw [inv_inv]
  field_simp

/-- A whole-plane complex analytic automorphism is affine with nonzero linear coefficient. -/
theorem plane_analytic_automorphism_affine (e : ℂ ≃ₜ ℂ) (ha : AnalyticOnNhd ℂ e Set.univ) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z : ℂ, e z = a * z + b := by
  obtain ⟨a, ha0, hlim⟩ := plane_analytic_automorphism_dslope_tendsto e ha
  have heD : Differentiable ℂ e := fun z => (ha z (Set.mem_univ _)).differentiableAt
  have hds : Differentiable ℂ (dslope e 0) := by
    apply differentiableOn_univ.mp
    exact (Complex.differentiableOn_dslope (Filter.univ_mem : (Set.univ : Set ℂ) ∈ 𝓝 0)).mpr
      heD.differentiableOn
  have heq : dslope e 0 = Function.const ℂ a := hds.eq_const_of_tendsto_cocompact hlim
  refine ⟨a, e 0, ha0, ?_⟩
  intro z
  have h := sub_smul_dslope e 0 z
  rw [heq] at h
  change (z - 0) * a = e z - e 0 at h
  rw [sub_zero] at h
  linear_combination -h

open scoped OnePoint
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces

/-- Agreement on the entire finite plane determines an actual Mobius map. -/
theorem mobius_eq_of_agree_plane (M N : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (h : ∀ z : ℂ, M.val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = N.val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) : M = N := by
  apply _root_.LowDimensionalTopology.Geometry.Mobius.mobius_eq_of_agree_triple M N ((0 : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    ((1 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ((2 : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) _ (h 0) (h 1) (h 2)
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro he
    have hh := OnePoint.coe_injective he
    norm_num at hh

/-- Each entire plane automorphism extends uniquely to an actual affine Mobius map fixing
infinity; existence follows from the proved affine classification. -/
theorem plane_analytic_automorphism_existsUnique_mobius (e : ℂ ≃ₜ ℂ)
    (ha : AnalyticOnNhd ℂ e Set.univ) :
    ∃! M : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, M.val ∞ = ∞ ∧
      ∀ z : ℂ, M.val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (e z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  obtain ⟨a, b, ha0, he⟩ := plane_analytic_automorphism_affine e ha
  let u : ℂˣ := Units.mk0 a ha0
  let M := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b * _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u
  have hM (z : ℂ) : M.val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (e z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
      b).val ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u).val (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) = _
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe, he z]
    rfl
  refine ⟨M, ⟨?_, hM⟩, ?_⟩
  · change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
    b).val ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u).val ∞) = ∞
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty]
  · intro N hN
    exact mobius_eq_of_agree_plane N M (fun z => (hN.2 z).trans (hM z).symm)

/-- The unique actual affine Mobius extension of an entire plane automorphism. -/
def planeAnalyticAutomorphismMobius (e : ℂ ≃ₜ ℂ) (ha : AnalyticOnNhd ℂ e Set.univ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup := (plane_analytic_automorphism_existsUnique_mobius
      e ha).choose

theorem planeAnalyticAutomorphismMobius_infty (e : ℂ ≃ₜ ℂ) (ha : AnalyticOnNhd ℂ e Set.univ) :
    (planeAnalyticAutomorphismMobius e ha).val ∞ = ∞ :=
  (plane_analytic_automorphism_existsUnique_mobius e ha).choose_spec.1.1

theorem planeAnalyticAutomorphismMobius_apply (e : ℂ ≃ₜ ℂ) (ha : AnalyticOnNhd ℂ e Set.univ) (z : ℂ) :
    (planeAnalyticAutomorphismMobius e ha).val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (e
      z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :=
  (plane_analytic_automorphism_existsUnique_mobius e ha).choose_spec.1.2 z

/-- A group acting by entire plane automorphisms has an actual affine Mobius representation. -/
def planeAnalyticActionMobiusHom {G : Type*} [Group G] (ρ : G →* (ℂ ≃ₜ ℂ))
    (ha : ∀ g, AnalyticOnNhd ℂ (ρ g)
      Set.univ) : G →* _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup where
  toFun g := planeAnalyticAutomorphismMobius (ρ g) (ha g)
  map_one' := by
    apply mobius_eq_of_agree_plane
    intro z
    rw [planeAnalyticAutomorphismMobius_apply, map_one]
    rfl
  map_mul' g h := by
    apply mobius_eq_of_agree_plane
    intro z
    rw [planeAnalyticAutomorphismMobius_apply, map_mul]
    change (((ρ g) ((ρ h) z) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
      (planeAnalyticAutomorphismMobius (ρ g) (ha g)).val
        ((planeAnalyticAutomorphismMobius (ρ h) (ha h)).val (z :
          _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    rw [planeAnalyticAutomorphismMobius_apply, planeAnalyticAutomorphismMobius_apply]

theorem planeAnalyticActionMobiusHom_injective {G : Type*} [Group G] (ρ : G →* (ℂ ≃ₜ ℂ))
    (ha : ∀ g, AnalyticOnNhd ℂ (ρ g) Set.univ) (hρ : Function.Injective ρ) :
    Function.Injective (planeAnalyticActionMobiusHom ρ ha) := by
  intro g h he
  apply hρ
  apply Homeomorph.ext
  intro z
  apply OnePoint.coe_injective
  have hv := congrArg (fun M : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup => M.val (z :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) he
  change (planeAnalyticAutomorphismMobius (ρ g) (ha g)).val (z :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
    (planeAnalyticAutomorphismMobius (ρ h) (ha h)).val (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hv
  simpa only [planeAnalyticAutomorphismMobius_apply] using hv

/-- In the canonical plane atlas, surface analyticity is exactly ordinary entire analyticity. -/
theorem complexPlaneRiemannSurface_analytic_iff (f : ℂ → ℂ) :
    RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas
      complexPlaneRiemannSurface.toRiemannAtlas f ↔ AnalyticOnNhd ℂ f Set.univ := by
  change RiemannAnalyticMap (globalChartRiemannAtlas (OpenPartialHomeomorph.refl ℂ) rfl)
    (globalChartRiemannAtlas (OpenPartialHomeomorph.refl ℂ) rfl) f ↔ _
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.globalChart_iff (OpenPartialHomeomorph.refl ℂ)
    rfl
    (OpenPartialHomeomorph.refl ℂ) rfl f]
  have hm : riemannChartMap (OpenPartialHomeomorph.refl ℂ) f (OpenPartialHomeomorph.refl ℂ) = f := rfl
  have hd : riemannChartMapDomain (OpenPartialHomeomorph.refl ℂ) f
      (OpenPartialHomeomorph.refl ℂ) = Set.univ := by
    simp [riemannChartMapDomain]
  rw [hm, hd]
  constructor
  · exact And.right
  · intro ha
    exact ⟨continuous_iff_continuousAt.mpr (fun z => (ha z (Set.mem_univ _)).continuousAt), ha⟩

/-- The canonical plane-surface automorphism has a unique actual affine Mobius extension. -/
theorem complexPlaneRiemannSurface_automorphism_existsUnique_mobius (e : ℂ ≃ₜ ℂ)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas
      complexPlaneRiemannSurface.toRiemannAtlas e) :
    ∃! M : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, M.val ∞ = ∞ ∧
      ∀ z : ℂ, M.val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (e z :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :=
  plane_analytic_automorphism_existsUnique_mobius e ((complexPlaneRiemannSurface_analytic_iff e).mp ha)

/-- The actual affine Mobius representation of the analytic plane-covering deck group. -/
def planeDeckMobiusHom {X : Type*} [TopologicalSpace X] (B : RiemannAtlas X)
    (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas B p) :
    deck p →* _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  planeAnalyticActionMobiusHom (deck p).subtype
    (fun g => (complexPlaneRiemannSurface_analytic_iff g.val).mp
      (covering_deck_analytic_of_analytic hp ha g))

theorem planeDeckMobiusHom_injective {X : Type*} [TopologicalSpace X] (B : RiemannAtlas X)
    (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas B p) :
    Function.Injective (planeDeckMobiusHom B p hp ha) :=
  planeAnalyticActionMobiusHom_injective _ _ Subtype.val_injective

theorem planeDeckMobiusHom_apply {X : Type*} [TopologicalSpace X] (B : RiemannAtlas X)
    (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas B p)
    (g : deck p) (z : ℂ) : (planeDeckMobiusHom B p hp ha g).val (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
      ((g • z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :=
  planeAnalyticAutomorphismMobius_apply g.val
    ((complexPlaneRiemannSurface_analytic_iff g.val).mp (covering_deck_analytic_of_analytic hp ha g)) z

/-- Freeness of the genuine deck action forces every affine image element to be a translation. -/
theorem planeDeckMobiusRange_translations {X : Type*} [TopologicalSpace X]
    (B : RiemannAtlas X) (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas B p)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f ∈ (planeDeckMobiusHom B p hp
      ha).range) :
    ∃ b : ℂ, f = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b := by
  obtain ⟨d, rfl⟩ := hf
  have had : AnalyticOnNhd ℂ d.val Set.univ := (complexPlaneRiemannSurface_analytic_iff d.val).mp
    (covering_deck_analytic_of_analytic hp ha d)
  obtain ⟨a, b, _ha0, hform⟩ := plane_analytic_automorphism_affine d.val had
  have ha1 : a = 1 := by
    by_contra hn
    have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
    let w : ℂ := b / (1 - a)
    have hfix : d • w = w := by
      change d.val w = w
      rw [hform w]
      dsimp [w]
      field_simp [hden]
      ring
    have hd1 : d = 1 := _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.covering_deck_fixedPoint_eq_one hp d w hfix
    have hzero := hform 0
    have hone := hform 1
    have hd0 : d.val 0 = 0 := congrArg (fun g : deck p => g.val 0) hd1
    have hdOne : d.val 1 = 1 := congrArg (fun g : deck p => g.val 1) hd1
    rw [hd0] at hzero
    rw [hdOne] at hone
    have hb0 : b = 0 := by simpa using hzero.symm
    rw [hb0] at hone
    exact hn (by simpa using hone.symm)
  refine ⟨b, mobius_eq_of_agree_plane _ _ ?_⟩
  intro z
  rw [planeDeckMobiusHom_apply, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
  congr 1
  change d.val z = z + b
  rw [hform z, ha1, one_mul]

/-- The actual affine Mobius deck image satisfies the ambient compact-set discontinuity
condition on the entire finite plane. -/
theorem planeDeckMobiusRange_discontinuous {X : Type*} [TopologicalSpace X] [T2Space X]
    (B : RiemannAtlas X) (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas B p) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn (planeDeckMobiusHom B p hp ha).range
      (Set.range ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) := by
  let H := (planeDeckMobiusHom B p hp ha).range
  let hT := planeDeckMobiusRange_translations B p hp ha
  let D := translationPlaneDomain H hT
  let φ := (planeDeckMobiusHom B p hp ha).ofInjective (planeDeckMobiusHom_injective B p hp ha)
  have hd : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous H D.carrier := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous.transport φ.toEquiv
    (translationPlaneHomeomorph H hT) (fun g z => by
      apply Subtype.ext
      change ((g • z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (planeDeckMobiusHom B p hp
        ha g).val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      exact (planeDeckMobiusHom_apply B p hp ha g z).symm) (covering_deck_discontinuous hp)
  exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_iff_subtype H D.carrier
    D.invariant).mpr hd

/-- The actual plane deck image contains no elliptic Mobius element. -/
theorem planeDeckMobiusRange_noElliptic {X : Type*} [TopologicalSpace X]
    (B : RiemannAtlas X) (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas B p)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f ∈ (planeDeckMobiusHom B p hp ha).range) : ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f := by
  intro hE
  obtain ⟨b, hb⟩ := planeDeckMobiusRange_translations B p hp ha f hf
  have hb0 : b ≠ 0 := by
    intro hz
    apply hE.1
    rw [hb, (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_eq_one_iff b).mpr hz]
  have hP : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f := hb.symm ▸ (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff b).mpr hb0
  exact hE.not_parabolic hP

end LowDimensionalTopology.Geometry.Surfaces
