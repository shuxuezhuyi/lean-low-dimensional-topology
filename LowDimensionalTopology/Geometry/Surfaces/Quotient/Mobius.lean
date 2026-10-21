module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Covering.PathLifting
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Covering
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Atlas
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusDiscontinuity
public import Mathlib.Topology.Algebra.ConstMulAction
public import LowDimensionalTopology.Geometry.Mobius.Classification.MobiusTypes
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.Discontinuity
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Covering.Deck
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteCyclicGroups
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Topology.Homeomorph.Quotient
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusLocalDomains
@[expose] public section
noncomputable section
open scoped Topology OnePoint
open Set Filter
namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces

/-- A genuine nonempty connected open domain of the Riemann sphere invariant under the specified actual Mobius subgroup. -/
structure MobiusInvariantDomain (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) where
  carrier : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
  isOpen : IsOpen carrier
  isConnected : IsConnected carrier
  invariant : ∀ (g : H) z, z ∈ carrier → g • z ∈ carrier

instance mobiusDomainAction {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  MobiusInvariantDomain H) :
    MulAction H D.carrier := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.invariantSubsetMulAction D.carrier D.invariant

instance mobiusDomainConnected {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  MobiusInvariantDomain H) :
    ConnectedSpace D.carrier := Subtype.connectedSpace D.isConnected

instance mobiusDomainLocallyCompact {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  MobiusInvariantDomain H) :
    LocallyCompactSpace D.carrier := D.isOpen.locallyCompactSpace

instance mobiusDomainContinuousConstSMul {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : MobiusInvariantDomain H) :
    ContinuousConstSMul H D.carrier where
  continuous_const_smul g := by
    apply Continuous.subtype_mk
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.continuous_mobiusBoundary g.val).comp continuous_subtype_val

/-- The orbit quotient carries its original quotient topology, including orbits with nontrivial finite stabilizer. -/
abbrev MobiusDomainQuotient {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  MobiusInvariantDomain H) :=
  Quotient (MulAction.orbitRel H D.carrier)

/-- The actual orbit quotient projection in the source quotient-surface construction. -/
def mobiusDomainProjection {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  MobiusInvariantDomain H) :
    D.carrier → MobiusDomainQuotient D := Quotient.mk _

theorem mobiusDomainProjection_surjective {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain H) : Function.Surjective (mobiusDomainProjection D) :=
  Quotient.mk_surjective

theorem mobiusDomainProjection_continuous {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain H) : Continuous (mobiusDomainProjection D) :=
  continuous_quot_mk

theorem mobiusDomainProjection_isOpenQuotientMap {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain H) : IsOpenQuotientMap (mobiusDomainProjection D) :=
  MulAction.isOpenQuotientMap_quotientMk

theorem mobiusDomainProjection_smul {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain H) (g : H) (z : D.carrier) :
    mobiusDomainProjection D (g • z) = mobiusDomainProjection D z := by
  apply Quotient.sound
  exact ⟨g, rfl⟩

/-- Every actual orbit quotient of a connected domain remains connected. -/
theorem mobiusDomainQuotient_connected {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain H) : ConnectedSpace (MobiusDomainQuotient D) := inferInstance

/-- The source compact-set discontinuity hypothesis gives Mathlib's exact properly discontinuous restricted action. -/
theorem mobiusDomain_properlyDiscontinuous {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain H) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      D.carrier) :
    ProperlyDiscontinuousSMul H D.carrier :=
  (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.isDiscontinuous_iff_properlyDiscontinuousSMul H
    D.carrier).mp
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_iff_subtype H D.carrier
      D.invariant).mp hD)

/-- topological part: actual quotients are Hausdorff even at elliptic fixed orbits. -/
theorem mobiusDomainQuotient_t2 {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain H) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      D.carrier) :
    T2Space (MobiusDomainQuotient D) := by
  let : ProperlyDiscontinuousSMul H D.carrier := mobiusDomain_properlyDiscontinuous D hD
  infer_instance

/-- Stabilizers in the genuine domain action are finite; they are not assumed trivial. -/
theorem mobiusDomain_stabilizer_finite {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain H) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      D.carrier) (z : D.carrier) :
    (MulAction.stabilizer H z : Set H).Finite := by
  let : ProperlyDiscontinuousSMul H D.carrier := mobiusDomain_properlyDiscontinuous D hD
  exact ProperlyDiscontinuousSMul.finite_stabilizer (Γ := H) z

open scoped unitInterval


/-- The actual orbit-quotient projection of a free discontinuous action is an unramified quotient covering. -/
theorem discontinuous_free_orbit_quotient_covering {Y G : Type*} [TopologicalSpace Y]
    [LocallyCompactSpace Y] [T2Space Y] [Group G] [MulAction G Y] [ContinuousConstSMul G Y]
    [IsCancelSMul G Y] (h : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous G Y) :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel G Y)) G := by
  let : ProperlyDiscontinuousSMul G Y := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.isDiscontinuous_iff_properlyDiscontinuousSMul G Y).mp h
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- An element fixing a point in a discontinuous action has finite order, derived from the genuinely finite stabilizer. -/
theorem discontinuous_fixed_element_isOfFinOrder {Y G : Type*} [TopologicalSpace Y]
    [Group G] [MulAction G Y] (h : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous G Y)
    (g : G) (y : Y) (hfix : g • y = y) : IsOfFinOrder g := by
  let S := MulAction.stabilizer G y
  have hS : (S : Set G).Finite := h.finite_stabilizer y
  let : Fintype S := hS.fintype
  let gs : S := ⟨g, hfix⟩
  exact S.subtype.isOfFinOrder (isOfFinOrder_of_finite gs)

/-- For a discontinuous action, absence of nontrivial finite-order elements implies a genuinely free action. -/
theorem discontinuous_noFiniteOrder_isCancelSMul {Y G : Type*} [TopologicalSpace Y]
    [Group G] [MulAction G Y] (h : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous G Y)
    (hfinite : ∀ g : G, IsOfFinOrder g → g = 1) : IsCancelSMul G Y := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g y hfix
  exact hfinite g (discontinuous_fixed_element_isOfFinOrder h g y hfix)

/-- A subgroup of actual Mobius transformations without elliptic elements has no nonidentity finite-order element. -/
theorem mobius_noElliptic_finite_order_eq_one (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (f : H) (hfin : IsOfFinOrder f) : f = 1 := by
  by_cases hf : (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) = 1
  · exact Subtype.ext hf
  · exact False.elim (hno f f.property hf
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic f hf (H.subtype.isOfFinOrder hfin)))

/-- The source's absence of elliptic transformations forces a discontinuous actual Mobius action to be free. -/
theorem mobius_discontinuous_noElliptic_isCancelSMul {Y : Type*} [TopologicalSpace Y]
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [MulAction H Y]
    (h : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous H Y)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) : IsCancelSMul H Y :=
  discontinuous_noFiniteOrder_isCancelSMul h (mobius_noElliptic_finite_order_eq_one H hno)

/-- The actual orbit quotient of a discontinuous Mobius group with no elliptic elements is a genuine unramified covering; freeness is derived from the source hypotheses. -/
theorem mobius_discontinuous_noElliptic_orbit_covering {Y : Type*} [TopologicalSpace Y]
    [LocallyCompactSpace Y] [T2Space Y] (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    [MulAction H Y] [ContinuousConstSMul H Y] (h :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous H Y)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel H Y)) H := by
  let := mobius_discontinuous_noElliptic_isCancelSMul H h hno
  exact discontinuous_free_orbit_quotient_covering h



/-- The actual domain itself has the restricted Riemann-sphere complex structure. -/
def mobiusDomainRiemannSurface {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  MobiusInvariantDomain H) :
    RiemannSurface D.carrier where
  toRiemannAtlas := sphereRiemannAtlas.liftLocalHomeomorph
    (Subtype.val : D.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) D.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  t2Space := inferInstance
  connectedSpace := inferInstance

/-- For the actual source action, absence of elliptic elements makes the original orbit projection a genuine covering map. -/
theorem mobiusDomain_noElliptic_covering {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain H) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      D.carrier)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) :
    IsQuotientCoveringMap (mobiusDomainProjection D) H :=
  mobius_discontinuous_noElliptic_orbit_covering H
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_iff_subtype H D.carrier
      D.invariant).mp hD) hno

/-- A genuine path joining a domain point to its actual Mobius translate projects to a closed loop. -/
def mobiusDomain_projected_loop {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain H) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      D.carrier)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (z : D.carrier) (g : H) (Γ : Path z (g • z)) :
    Path (mobiusDomainProjection D z) (mobiusDomainProjection D z) :=
  _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.quotientCoveringProjectedLoop (mobiusDomain_noElliptic_covering D hD hno) z g Γ

/-- Every actual quotient loop lifts to a path ending at a unique element's translate of its initial domain point. -/
theorem mobiusDomain_loop_lift_endpoint {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain H) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      D.carrier)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (z : D.carrier) (γ : Path (mobiusDomainProjection D z) (mobiusDomainProjection D z)) :
    ∃! g : H, (mobiusDomain_noElliptic_covering D hD hno).isCoveringMap.liftPath γ z γ.source 1 = g • z :=
  _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.quotientCovering_closed_loop_lift_endpoint (mobiusDomain_noElliptic_covering D hD hno) z γ

/-- In the actual domain quotient, every continuous lift of a nullhomotopic loop closes and its represented group element is the identity. -/
theorem mobiusDomain_nullhomotopic_loop_endpoint {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain H) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      D.carrier)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (z : D.carrier) (γ : Path (mobiusDomainProjection D z) (mobiusDomainProjection D z))
    (hγ : γ.Homotopic (Path.refl (mobiusDomainProjection D z)))
    (Γ : C(I, D.carrier)) (hΓ : mobiusDomainProjection D ∘ Γ = γ)
    (hΓ0 : Γ 0 = z) (g : H) (hΓ1 : Γ 1 = g • z) : Γ 1 = z ∧ g = 1 := by
  let hp := mobiusDomain_noElliptic_covering D hD hno
  exact ⟨_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.covering_nullhomotopic_any_lift_closed
    hp.isCoveringMap z γ hγ Γ hΓ hΓ0,
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.quotientCovering_nullhomotopic_endpoint_eq_one hp z γ hγ Γ hΓ hΓ0 g hΓ1⟩

/-- An actual Mobius group is Fuchsian exactly when it acts discontinuously on some invariant genuine generalized disc. -/
def IsFuchsianGroup (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Prop :=
  ∃ D : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D ∧
    (∀ (g : H) z, z ∈ D → g • z ∈ D) ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H D


open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius

/-- The actual reciprocal Mobius permutation is exactly the reciprocal used by the sphere's complex atlas. -/
theorem sphereReciprocal_eq_mobius (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    sphereReciprocal z = _root_.LowDimensionalTopology.Geometry.Mobius.reciprocalMobius.val z := by
  change sphereReciprocal z = _root_.LowDimensionalTopology.Geometry.Mobius.reciprocal z
  induction z using OnePoint.rec with
  | infty => rw [sphereReciprocal_infty, _root_.LowDimensionalTopology.Geometry.Mobius.reciprocal_infty]
  | coe z =>
    by_cases hz : z = 0
    · subst z
      rw [sphereReciprocal_zero, _root_.LowDimensionalTopology.Geometry.Mobius.reciprocal_zero]
    · rw [sphereReciprocal_coe z hz, _root_.LowDimensionalTopology.Geometry.Mobius.reciprocal_coe z hz]

/-- The finite-to-finite expression of every actual Mobius transformation is holomorphic on its exact chart domain. -/
theorem mobius_finite_chart_analytic (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    AnalyticOnNhd ℂ (riemannChartMap sphereFiniteChart f.val sphereFiniteChart)
      (riemannChartMapDomain sphereFiniteChart f.val sphereFiniteChart) := by
  obtain ⟨A, rfl⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusMatrixProjection_surjective f
  let D := riemannChartMapDomain sphereFiniteChart (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusMatrixProjection
    A).val sphereFiniteChart
  let R : ℂ → ℂ := fun z => (A 0 0 * z + A 0 1) / (A 1 0 * z + A 1 1)
  have hne (z : ℂ) (hz : z ∈ D) : A 1 0 * z + A 1 1 ≠ 0 := by
    have hs := hz.2
    change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusMatrixProjection A).val (sphereFiniteChart.symm
      z) ∈ sphereFiniteChart.source at hs
    rw [sphereFiniteChart_symm, sphereFiniteChart_source] at hs
    change _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear A z ≠ ∞ at hs
    intro he
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_coe, ite_eq_left he] at hs
    exact hs rfl
  have hR : AnalyticOnNhd ℂ R D := by
    intro z hz
    have hn : AnalyticAt ℂ (fun w : ℂ => A 0 0 * w + A 0 1) z := by fun_prop
    have hd : AnalyticAt ℂ (fun w : ℂ => A 1 0 * w + A 1 1) z := by fun_prop
    exact hn.div hd (hne z hz)
  apply AnalyticOnNhd.congr
    (riemannChartMapDomain_isOpen sphereFiniteChart
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusMatrixProjection A).val sphereFiniteChart
      (_root_.LowDimensionalTopology.Geometry.Mobius.continuous_mobiusBoundary _)) hR
  intro z hz
  change R z = sphereFiniteChart ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusMatrixProjection A).val
    (sphereFiniteChart.symm z))
  rw [sphereFiniteChart_symm]
  change R z = sphereFiniteChart (_root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear A z)
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_coe, ite_eq_right (hne z hz),
    sphereFiniteChart_coe]

/-- Moving the target infinity chart is postcomposition by the actual reciprocal map. -/
theorem riemannChartMap_infinity_target (e : OpenPartialHomeomorph
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex ℂ)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    riemannChartMap e f.val sphereInfinityChart =
      riemannChartMap e (_root_.LowDimensionalTopology.Geometry.Mobius.reciprocalMobius * f).val sphereFiniteChart := by
  funext z
  change sphereFiniteChart (sphereReciprocal (f.val (e.symm z))) =
    sphereFiniteChart (_root_.LowDimensionalTopology.Geometry.Mobius.reciprocalMobius.val (f.val (e.symm z)))
  rw [sphereReciprocal_eq_mobius]

theorem riemannChartMapDomain_infinity_target (e : OpenPartialHomeomorph
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex ℂ)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    riemannChartMapDomain e f.val sphereInfinityChart =
      riemannChartMapDomain e (_root_.LowDimensionalTopology.Geometry.Mobius.reciprocalMobius * f).val sphereFiniteChart := by
  ext z
  simp only [riemannChartMapDomain, Set.mem_inter_iff, Set.mem_preimage,
    sphereInfinityChart_source, sphereFiniteChart_source, Set.mem_compl_iff, Set.mem_singleton_iff]
  change (z ∈ e.target ∧ f.val (e.symm z) ≠ (0 : ℂ)) ↔
    (z ∈ e.target ∧ _root_.LowDimensionalTopology.Geometry.Mobius.reciprocalMobius.val (f.val (e.symm z)) ≠ ∞)
  rw [← sphereReciprocal_eq_mobius]
  exact and_congr_right fun _ => (not_congr (sphereReciprocal_eq_infty_iff _)).symm

/-- Moving the source infinity chart is precomposition by the actual reciprocal map. -/
theorem riemannChartMap_infinity_source (g : OpenPartialHomeomorph
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex ℂ)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    riemannChartMap sphereInfinityChart f.val g =
      riemannChartMap sphereFiniteChart (f * _root_.LowDimensionalTopology.Geometry.Mobius.reciprocalMobius).val g := by
  funext z
  change g (f.val (sphereReciprocal (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))) =
    g (f.val (_root_.LowDimensionalTopology.Geometry.Mobius.reciprocalMobius.val (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)))
  rw [sphereReciprocal_eq_mobius]

theorem riemannChartMapDomain_infinity_source (g : OpenPartialHomeomorph
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex ℂ)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    riemannChartMapDomain sphereInfinityChart f.val g =
      riemannChartMapDomain sphereFiniteChart (f * _root_.LowDimensionalTopology.Geometry.Mobius.reciprocalMobius).val g := by
  ext z
  simp only [riemannChartMapDomain, sphereInfinityChart_target, sphereFiniteChart_target,
    Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_preimage,
    sphereInfinityChart_symm, sphereFiniteChart_symm]
  change f.val (sphereReciprocal (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ∈ g.source ↔
    f.val (_root_.LowDimensionalTopology.Geometry.Mobius.reciprocalMobius.val (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ∈ g.source
  rw [sphereReciprocal_eq_mobius]

/-- Every actual Mobius transformation acts analytically on the geometric genuine two-chart Riemann sphere. -/
theorem mobius_riemannSphere_analytic (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    RiemannAnalyticMap sphereRiemannAtlas sphereRiemannAtlas f.val := by
  refine ⟨_root_.LowDimensionalTopology.Geometry.Mobius.continuous_mobiusBoundary f, ?_⟩
  intro e he g hg
  change e ∈ sphereCharts at he
  change g ∈ sphereCharts at hg
  simp only [sphereCharts, Set.mem_insert_iff, Set.mem_singleton_iff] at he hg
  rcases he with rfl | rfl
  · rcases hg with rfl | rfl
    · exact mobius_finite_chart_analytic f
    · rw [riemannChartMap_infinity_target, riemannChartMapDomain_infinity_target]
      exact mobius_finite_chart_analytic _
  · rcases hg with rfl | rfl
    · rw [riemannChartMap_infinity_source, riemannChartMapDomain_infinity_source]
      exact mobius_finite_chart_analytic _
    · rw [riemannChartMap_infinity_source, riemannChartMapDomain_infinity_source,
        riemannChartMap_infinity_target, riemannChartMapDomain_infinity_target]
      exact mobius_finite_chart_analytic _


open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces

/-- A finite complex multiplicative subgroup consists of all roots of unity of its order. -/
theorem finiteComplexUnits_eq_rootsOfUnity (K : Subgroup ℂˣ) [Finite K] :
    K = rootsOfUnity (Nat.card K) ℂ := by
  let : NeZero (Nat.card K) := ⟨Nat.card_pos.ne'⟩
  apply Subgroup.eq_of_le_of_card_ge
  · intro a ha
    rw [mem_rootsOfUnity]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨a, ha⟩ : K)))
  · rw [Complex.card_rootsOfUnity]

/-- Equality of the power coordinate is precisely equivalence under the finite rotation group,
including the branched point zero. -/
theorem finiteComplexUnits_pow_eq_iff (K : Subgroup ℂˣ) [Finite K] (z w : ℂ) :
    z ^ Nat.card K = w ^ Nat.card K ↔ ∃ a ∈ K, (a : ℂ) * z = w := by
  have hn : Nat.card K ≠ 0 := Nat.card_pos.ne'
  constructor
  · intro hzw
    by_cases hz : z = 0
    · have hw : w = 0 := (pow_eq_zero_iff hn).mp (by simpa [hz, zero_pow hn] using hzw.symm)
      exact ⟨1, K.one_mem, by simp [hz, hw]⟩
    · have hw : w ≠ 0 := by
        intro hw
        exact hz ((pow_eq_zero_iff hn).mp (by simpa [hw, zero_pow hn] using hzw))
      let a : ℂˣ := Units.mk0 (w / z) (div_ne_zero hw hz)
      refine ⟨a, ?_, ?_⟩
      · rw [finiteComplexUnits_eq_rootsOfUnity K, mem_rootsOfUnity']
        change (w / z) ^ Nat.card K = 1
        rw [div_pow, ← hzw, div_self (pow_ne_zero _ hz)]
      · change w / z * z = w
        exact div_mul_cancel₀ w hz
  · rintro ⟨a, ha, rfl⟩
    have hpow : (a : ℂ) ^ Nat.card K = 1 :=
      (mem_rootsOfUnity' _ _).mp (by rwa [← finiteComplexUnits_eq_rootsOfUnity K])
    rw [mul_pow, hpow, one_mul]

/-- The power map sends the full round disc onto the round disc of the powered radius. -/
theorem complex_pow_image_ball (n : ℕ) (hn : n ≠ 0) (r : ℝ) (hr : 0 ≤ r) :
    (fun z : ℂ => z ^ n) '' Metric.ball (0 : ℂ) r = Metric.ball (0 : ℂ) (r ^ n) := by
  let : NeZero n := ⟨hn⟩
  ext z
  simp only [Metric.mem_ball, dist_zero_right, Set.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [norm_pow]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hr hn).mpr hw
  · intro hz
    obtain ⟨w, rfl⟩ := (Complex.isOpenQuotientMap_pow n).surjective z
    refine ⟨w, ?_, rfl⟩
    rw [norm_pow] at hz
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hr hn).mp hz

/-- The actual finite Mobius subgroup identifies precisely the fibers of the power coordinate. -/
theorem finiteMobius_rotation_pow_eq_iff (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (hi : H ≤ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer) (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 :
      ℂ)) (z w : ℂ) :
    z ^ Nat.card H = w ^ Nat.card H ↔
      ∃ f ∈ H, f.val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  let ϕ := _root_.LowDimensionalTopology.Geometry.Mobius.subgroupMultiplierHom H hi
  let K := _root_.LowDimensionalTopology.Geometry.Mobius.subgroupMultiplierRange H hi
  have hinj : Function.Injective ϕ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.subgroupMultiplierHom_injective_of_fix_zero H hi hz
  let e : H ≃* K := MonoidHom.ofInjective hinj
  let : Finite K := Finite.of_surjective e e.surjective
  have hcard : Nat.card H = Nat.card K := Nat.card_congr e.toEquiv
  rw [hcard, finiteComplexUnits_pow_eq_iff K z w]
  constructor
  · rintro ⟨a, ha, haw⟩
    obtain ⟨f, hf⟩ := ha
    refine ⟨f.val, f.property, ?_⟩
    have hformula := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_affine_formula (⟨f.val, hi f.property⟩ :
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer) z
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusAffineConstant_zero_of_fix_zero _ (hz _ f.property),
      add_zero] at hformula
    change f.val.val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = _
    change f.val.val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (((ϕ f : ℂˣ) : ℂ) * z :
      ℂ) at hformula
    rw [hformula, hf, haw]
  · rintro ⟨f, hf, hfw⟩
    let g : H := ⟨f, hf⟩
    refine ⟨ϕ g, ⟨g, rfl⟩, ?_⟩
    have hformula := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_affine_formula (⟨f, hi hf⟩ :
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer) z
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusAffineConstant_zero_of_fix_zero _ (hz _ hf),
      add_zero] at hformula
    exact OnePoint.coe_injective (hformula.symm.trans hfw)

/-- The restricted power map between the two actual open Euclidean discs. -/
def complexDiscPower (n : ℕ) (hn : n ≠ 0) (r : ℝ) (hr : 0 ≤ r) :
    Metric.ball (0 : ℂ) r → Metric.ball (0 : ℂ) (r ^ n) :=
  fun z => ⟨z.val ^ n, by
    have hz : ‖z.val‖ < r := mem_ball_zero_iff.mp z.property
    rw [Metric.mem_ball, dist_zero_right, norm_pow]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hr hn).mpr hz⟩

theorem complexDiscPower_isOpenQuotientMap (n : ℕ) (hn : n ≠ 0) (r : ℝ) (hr : 0 ≤ r) :
    IsOpenQuotientMap (complexDiscPower n hn r hr) := by
  let : NeZero n := ⟨hn⟩
  have hp := Complex.isOpenQuotientMap_pow n
  refine ⟨?_, ?_, ?_⟩
  · intro z
    have hz : z.val ∈ (fun w : ℂ => w ^ n) '' Metric.ball (0 : ℂ) r := by
      rw [complex_pow_image_ball n hn r hr]
      exact z.property
    obtain ⟨w, hw, heq⟩ := hz
    exact ⟨⟨w, hw⟩, Subtype.ext heq⟩
  · exact (hp.continuous.comp continuous_subtype_val).subtype_mk _
  · exact hp.isOpenMap.mapsToRestrict Metric.isOpen_ball
      (fun _ hz => (complexDiscPower n hn r hr ⟨_, hz⟩).property)

/-- The orbit relation on the round disc is the actual ambient rotation orbit relation. -/
def finiteRotationDiscSetoid (K : Subgroup ℂˣ) (r : ℝ) : Setoid (Metric.ball (0 : ℂ) r) :=
  (MulAction.orbitRel K ℂ).comap Subtype.val

theorem finiteRotationDiscSetoid_iff (K : Subgroup ℂˣ) [Finite K] (r : ℝ)
    (z w : Metric.ball (0 : ℂ) r) :
    finiteRotationDiscSetoid K r z w ↔ z.val ^ Nat.card K = w.val ^ Nat.card K := by
  change z.val ∈ MulAction.orbit K w.val ↔ _
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ((finiteComplexUnits_pow_eq_iff K w.val z.val).mpr ⟨a.val, a.property, ha⟩).symm
  · intro hz
    obtain ⟨a, ha, haw⟩ := (finiteComplexUnits_pow_eq_iff K w.val z.val).mp hz.symm
    exact ⟨⟨a, ha⟩, haw⟩

/-- The branched power coordinate is a true homeomorphism from the finite rotation quotient
of the disc onto a disc, including the image of zero. -/
def finiteRotationDiscHomeomorph (K : Subgroup ℂˣ) [Finite K] (r : ℝ) (hr : 0 ≤ r) :
    Quotient (finiteRotationDiscSetoid K r) ≃ₜ Metric.ball (0 : ℂ) (r ^ Nat.card K) := by
  let hp := complexDiscPower_isOpenQuotientMap (Nat.card K) Nat.card_pos.ne' r hr
  let F : C(Metric.ball (0 : ℂ) r, Metric.ball (0 : ℂ) (r ^ Nat.card K)) :=
    ⟨complexDiscPower (Nat.card K) Nat.card_pos.ne' r hr, hp.continuous⟩
  have hF : Topology.IsQuotientMap F := hp.isQuotientMap
  have hrel (z w : Metric.ball (0 : ℂ) r) :
      finiteRotationDiscSetoid K r z w ↔ Setoid.ker F z w := by
    rw [finiteRotationDiscSetoid_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  exact (Homeomorph.Quotient.congrRight hrel).trans hF.homeomorph

theorem finiteRotationDiscHomeomorph_apply_mk (K : Subgroup ℂˣ) [Finite K] (r : ℝ) (hr : 0 ≤ r)
    (z : Metric.ball (0 : ℂ) r) :
    (finiteRotationDiscHomeomorph K r hr (Quotient.mk _ z)).val = z.val ^ Nat.card K := rfl

/-- The orbit relation here uses the actual Mobius action on the Riemann sphere. -/
def finiteMobiusRotationDiscSetoid (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (r :
  ℝ) :
    Setoid (Metric.ball (0 : ℂ) r) :=
  (MulAction.orbitRel H _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap (fun z => (z.val :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))

theorem finiteMobiusRotationDiscSetoid_iff (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (hi : H ≤ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer) (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 :
      ℂ)) (r : ℝ)
    (z w : Metric.ball (0 : ℂ) r) :
    finiteMobiusRotationDiscSetoid H r z w ↔ z.val ^ Nat.card H = w.val ^ Nat.card H := by
  change (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ MulAction.orbit H (w.val :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ↔ _
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ((finiteMobius_rotation_pow_eq_iff H hi hz w.val z.val).mpr
      ⟨a.val, a.property, ha⟩).symm
  · intro hzw
    obtain ⟨a, ha, haw⟩ := (finiteMobius_rotation_pow_eq_iff H hi hz w.val z.val).mp hzw.symm
    exact ⟨⟨a, ha⟩, haw⟩

/-- The local branched quotient coordinate for the actual finite Mobius rotation subgroup. -/
def finiteMobiusRotationDiscHomeomorph (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (hi : H ≤ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer) (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 :
      ℂ))
    (r : ℝ) (hr : 0 ≤ r) :
    Quotient (finiteMobiusRotationDiscSetoid H r) ≃ₜ Metric.ball (0 : ℂ) (r ^ Nat.card H) := by
  let hp := complexDiscPower_isOpenQuotientMap (Nat.card H) Nat.card_pos.ne' r hr
  let F : C(Metric.ball (0 : ℂ) r, Metric.ball (0 : ℂ) (r ^ Nat.card H)) :=
    ⟨complexDiscPower (Nat.card H) Nat.card_pos.ne' r hr, hp.continuous⟩
  have hF : Topology.IsQuotientMap F := hp.isQuotientMap
  have hrel (z w : Metric.ball (0 : ℂ) r) :
      finiteMobiusRotationDiscSetoid H r z w ↔ Setoid.ker F z w := by
    rw [finiteMobiusRotationDiscSetoid_iff H hi hz]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  exact (Homeomorph.Quotient.congrRight hrel).trans hF.homeomorph

theorem finiteMobiusRotationDiscHomeomorph_apply_mk (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (hi : H ≤ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer) (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 :
      ℂ))
    (r : ℝ) (hr : 0 ≤ r) (z : Metric.ball (0 : ℂ) r) :
    (finiteMobiusRotationDiscHomeomorph H hi hz r hr (Quotient.mk _ z)).val =
      z.val ^ Nat.card H := rfl

theorem complex_power_coordinate_analytic (n : ℕ) : AnalyticOnNhd ℂ (fun z : ℂ => z ^ n) Set.univ :=
  fun _z _ => analyticAt_id.pow n

theorem complex_power_coordinate_deriv_ne_zero (n : ℕ) (hn : n ≠ 0) (z : ℂ) (hz : z ≠ 0) :
    deriv (fun w : ℂ => w ^ n) z ≠ 0 := by
  rw [deriv_pow_field]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hn) (pow_ne_zero _ hz)

/-- The actual Mobius chart followed by the finite chart of the Riemann sphere. -/
def mobiusNormalizedDiscChart (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : OpenPartialHomeomorph _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex ℂ :=
  (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
    q).toOpenPartialHomeomorph.trans sphereFiniteChart

theorem mobiusNormalizedDiscChart_source (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (r :
  ℝ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r ⊆ (mobiusNormalizedDiscChart q).source := by
  rintro z ⟨w, ⟨v, _hv, rfl⟩, rfl⟩
  refine ⟨Set.mem_univ _, ?_⟩
  rw [sphereFiniteChart_source]
  change q.val (q.val.symm (v : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ≠ ∞
  rw [Equiv.apply_symm_apply]
  exact OnePoint.coe_ne_infty _

theorem mobiusNormalizedDiscChart_image (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (r : ℝ) :
    mobiusNormalizedDiscChart q '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r = Metric.ball (0 : ℂ) r := by
  ext z
  constructor
  · rintro ⟨w, ⟨v, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
    change sphereFiniteChart (q.val (q.val.symm (u :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))) ∈ Metric.ball (0 : ℂ) r
    rwa [Equiv.apply_symm_apply, sphereFiniteChart_coe]
  · intro hz
    refine ⟨q.val.symm (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ⟨(z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
    change sphereFiniteChart (q.val (q.val.symm (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))) = z
    rw [Equiv.apply_symm_apply, sphereFiniteChart_coe]

/-- The original round disc is homeomorphic to the literal Euclidean disc under its normalizer. -/
def mobiusNormalizedDiscHomeomorph (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (r : ℝ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r ≃ₜ Metric.ball (0 : ℂ) r :=
  (mobiusNormalizedDiscChart q).homeomorphOfImageSubsetSource
    (mobiusNormalizedDiscChart_source q r) (mobiusNormalizedDiscChart_image q r)

theorem mobiusNormalizedDiscHomeomorph_coe (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (r :
  ℝ)
    (z : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) :
    q.val z.val = ((mobiusNormalizedDiscHomeomorph q r z).val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  have hz := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusNormalizedDisc q r z.val).mp z.property
  obtain ⟨w, _hw, hweq⟩ := hz
  change q.val z.val = (sphereFiniteChart (q.val z.val) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  rw [← hweq, sphereFiniteChart_coe]

theorem mobiusNormalizedDiscHomeomorph_symm_coe (q :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (r : ℝ)
    (z : Metric.ball (0 : ℂ) r) :
    ((mobiusNormalizedDiscHomeomorph q r).symm z).val = q.val.symm (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  apply q.val.injective
  rw [mobiusNormalizedDiscHomeomorph_coe, Homeomorph.apply_symm_apply, Equiv.apply_symm_apply]

/-- The original actual Mobius orbit relation restricted to the normalized round disc. -/
def mobiusNormalizedDiscOrbitSetoid (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (q :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (r : ℝ) : Setoid (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) :=
  (MulAction.orbitRel H _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap Subtype.val

theorem mobiusNormalizedDiscOrbitSetoid_conjugate (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (r : ℝ) (z w :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) :
    mobiusNormalizedDiscOrbitSetoid H q r z w ↔
      finiteMobiusRotationDiscSetoid (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) r
        (mobiusNormalizedDiscHomeomorph q r z) (mobiusNormalizedDiscHomeomorph q r w) := by
  change z.val ∈ MulAction.orbit H w.val ↔
    (((mobiusNormalizedDiscHomeomorph q r z).val : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈
      MulAction.orbit (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H)
        (((mobiusNormalizedDiscHomeomorph q r w).val : ℂ) :
          _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  rw [← mobiusNormalizedDiscHomeomorph_coe, ← mobiusNormalizedDiscHomeomorph_coe]
  simp only [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨⟨q * a.val * q⁻¹,
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr
      ⟨a.val, a.property, rfl⟩⟩, ?_⟩
    change q.val (a.val.val (q.val.symm (q.val w.val))) = q.val z.val
    rw [Equiv.symm_apply_apply]
    exact congrArg q.val ha
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb, hba⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H a.val).mp a.property
    refine ⟨⟨b, hb⟩, q.val.injective ?_⟩
    change q.val (b.val w.val) = q.val z.val
    change a.val.val (q.val w.val) = q.val z.val at ha
    rw [← hba] at ha
    change q.val (b.val (q.val.symm (q.val w.val))) = q.val z.val at ha
    simpa only [Equiv.symm_apply_apply] using ha

/-- The original finite stabilizer quotient is a genuine round disc, with its actual quotient topology. -/
def mobiusNormalizedDiscOrbitHomeomorph (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hi : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H ≤
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H, f.val (0 :
      ℂ) = (0 : ℂ))
    (r : ℝ) (hr : 0 ≤ r) :
    Quotient (mobiusNormalizedDiscOrbitSetoid H q r) ≃ₜ
      Metric.ball (0 : ℂ) (r ^ Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H)) := by
  let e : H ≃* _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  let : Finite (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
    H) := Finite.of_surjective e e.surjective
  exact (Homeomorph.Quotient.congr (mobiusNormalizedDiscHomeomorph q r)
    (mobiusNormalizedDiscOrbitSetoid_conjugate H q r)).trans
    (finiteMobiusRotationDiscHomeomorph
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) hi hz r hr)

theorem mobiusNormalizedDiscOrbitHomeomorph_apply_mk (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hi : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H ≤
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H, f.val (0 :
      ℂ) = (0 : ℂ))
    (r : ℝ) (hr : 0 ≤ r) (z : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) :
    (mobiusNormalizedDiscOrbitHomeomorph H q hi hz r hr (Quotient.mk _ z)).val =
      (mobiusNormalizedDiscHomeomorph q r
        z).val ^ Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
        H) := rfl

/-- The actual full-group quotient projection restricted to a subset of its invariant domain. -/
def mobiusDiscDomainProjection {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  MobiusInvariantDomain G)
    (N : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hND : N ⊆
      D.carrier) : N → MobiusDomainQuotient D :=
  fun z => mobiusDomainProjection D ⟨z.val, hND z.property⟩

/-- The image of that small disc in the actual full-group orbit quotient. -/
def mobiusDiscQuotientImage {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  MobiusInvariantDomain G)
    (N : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hND : N ⊆
      D.carrier) : Set (MobiusDomainQuotient D) :=
  Set.range (mobiusDiscDomainProjection D N hND)

def mobiusDiscRangeProjection {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  MobiusInvariantDomain G)
    (N : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hND : N ⊆
      D.carrier) : N → mobiusDiscQuotientImage D N hND :=
  fun z => ⟨mobiusDiscDomainProjection D N hND z, ⟨z, rfl⟩⟩

theorem mobiusDiscDomainProjection_continuous {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (N : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hND : N ⊆
      D.carrier) :
    Continuous (mobiusDiscDomainProjection D N hND) :=
  (mobiusDomainProjection_continuous D).comp (continuous_subtype_val.subtype_mk _)

theorem mobiusDiscDomainProjection_isOpenMap {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (N : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hND : N ⊆
      D.carrier) (hN : IsOpen N) :
    IsOpenMap (mobiusDiscDomainProjection D N hND) :=
  (mobiusDomainProjection_isOpenQuotientMap D).isOpenMap.comp
    (hN.isOpenEmbedding_subtypeVal.isOpenMap.codRestrict (fun z => hND z.property))

theorem mobiusDiscQuotientImage_isOpen {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (N : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hND : N ⊆
      D.carrier) (hN : IsOpen N) :
    IsOpen (mobiusDiscQuotientImage D N hND) :=
  (mobiusDiscDomainProjection_isOpenMap D N hND hN).isOpen_range

theorem mobiusDiscRangeProjection_isOpenQuotientMap {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (N : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hND : N ⊆
      D.carrier) (hN : IsOpen N) :
    IsOpenQuotientMap (mobiusDiscRangeProjection D N hND) := by
  refine ⟨?_, (mobiusDiscDomainProjection_continuous D N hND).subtype_mk _,
    (mobiusDiscDomainProjection_isOpenMap D N hND hN).codRestrict _⟩
  rintro ⟨z, w, rfl⟩
  exact ⟨w, rfl⟩

/-- Separation from non-stabilizer translates identifies the restricted orbit quotient with
the actual open image in the full-group quotient. -/
def mobiusDiscOrbitQuotientHomeomorph {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (N : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hND : N ⊆ D.carrier) (hN : IsOpen N) (hKG :
      K ≤ G)
    (hsep : ∀ g ∈ G, g ∉ K → Disjoint (g.val '' N) N) :
    Quotient ((MulAction.orbitRel K _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap (Subtype.val :
      N → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ≃ₜ
      mobiusDiscQuotientImage D N hND := by
  let hp := mobiusDiscRangeProjection_isOpenQuotientMap D N hND hN
  let F : C(N, mobiusDiscQuotientImage D N hND) :=
    ⟨mobiusDiscRangeProjection D N hND, hp.continuous⟩
  have hF : Topology.IsQuotientMap F := hp.isQuotientMap
  have hrel (z w : N) :
      (MulAction.orbitRel K _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap (Subtype.val : N →
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) z w ↔
        Setoid.ker F z w := by
    constructor
    · rintro ⟨k, hk⟩
      apply Subtype.ext
      apply Quotient.sound
      refine ⟨⟨k.val, hKG k.property⟩, Subtype.ext ?_⟩
      exact hk
    · intro hzw
      have he : mobiusDiscDomainProjection D N hND z = mobiusDiscDomainProjection D N hND w :=
        congrArg Subtype.val hzw
      obtain ⟨g, hg⟩ := Quotient.exact he
      have hgw : g.val.val w.val = z.val := congrArg Subtype.val hg
      have hgK : g.val ∈ K := by
        by_contra hn
        exact Set.disjoint_left.mp (hsep g.val g.property hn)
          ⟨w.val, w.property, rfl⟩ (by rw [hgw]; exact z.property)
      exact ⟨⟨g.val, hgK⟩, hgw⟩
  exact (Homeomorph.Quotient.congrRight hrel).trans hF.homeomorph

theorem mobiusDiscOrbitQuotientHomeomorph_apply_mk {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (N : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hND : N ⊆ D.carrier) (hN : IsOpen N) (hKG :
      K ≤ G)
    (hsep : ∀ g ∈ G, g ∉ K → Disjoint (g.val '' N) N) (z : N) :
    mobiusDiscOrbitQuotientHomeomorph D K N hND hN hKG hsep (Quotient.mk _ z) =
      mobiusDiscRangeProjection D N hND z := rfl

/-- The actual open image of a round disc in the full-group quotient has the branched power chart. -/
def mobiusDiscQuotientBranchHomeomorph {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (K : Subgroup
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite K]
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hi :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K ≤
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K, f.val (0 :
      ℂ) = (0 : ℂ))
    (r : ℝ) (hr : 0 < r) (hND : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r ⊆
      D.carrier) (hKG : K ≤ G)
    (hsep : ∀ g ∈ G, g ∉ K → Disjoint (g.val ''
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r)
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r)) :
    mobiusDiscQuotientImage D (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) hND ≃ₜ
      Metric.ball (0 : ℂ) (r ^ Nat.card
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K)) :=
  (mobiusDiscOrbitQuotientHomeomorph D K (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q
    r) hND
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc_isComplexOpenDisc q
      hr).isOpen hKG hsep).symm.trans
    (mobiusNormalizedDiscOrbitHomeomorph K q hi hz r hr.le)

theorem mobiusDiscQuotientBranchHomeomorph_apply_projection {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (K : Subgroup
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite K]
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hi :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K ≤
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K, f.val (0 :
      ℂ) = (0 : ℂ))
    (r : ℝ) (hr : 0 < r) (hND : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r ⊆
      D.carrier) (hKG : K ≤ G)
    (hsep : ∀ g ∈ G, g ∉ K → Disjoint (g.val ''
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r)
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r))
    (z : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) :
    (mobiusDiscQuotientBranchHomeomorph D K q hi hz r hr hND hKG hsep
      (mobiusDiscRangeProjection D (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) hND
        z)).val =
      (mobiusNormalizedDiscHomeomorph q r z).val ^ Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K) := by
  have hm := mobiusDiscOrbitQuotientHomeomorph_apply_mk D K (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) hND
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc_isComplexOpenDisc q
      hr).isOpen hKG hsep z
  change ((mobiusNormalizedDiscOrbitHomeomorph K q hi hz r hr.le)
    ((mobiusDiscOrbitQuotientHomeomorph D K (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc
      q r) hND
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc_isComplexOpenDisc q
        hr).isOpen hKG hsep).symm
      (mobiusDiscRangeProjection D (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) hND
        z))).val = _
  rw [← hm, Homeomorph.symm_apply_apply]
  rfl

/-- A genuine branch chart on an open subset of the actual full-group quotient. -/
def mobiusDiscQuotientBranchChart {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (K : Subgroup
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite K]
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hi :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K ≤
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K, f.val (0 :
      ℂ) = (0 : ℂ))
    (r : ℝ) (hr : 0 < r) (hND : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r ⊆
      D.carrier) (hKG : K ≤ G)
    (hsep : ∀ g ∈ G, g ∉ K → Disjoint (g.val ''
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r)
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r)) :
    OpenPartialHomeomorph (MobiusDomainQuotient D) ℂ := by
  let S : TopologicalSpace.Opens (MobiusDomainQuotient D) :=
    ⟨mobiusDiscQuotientImage D (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) hND,
      mobiusDiscQuotientImage_isOpen D _ hND (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc_isComplexOpenDisc q hr).isOpen⟩
  let T : TopologicalSpace.Opens ℂ :=
    ⟨Metric.ball (0 : ℂ) (r ^ Nat.card
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K)), Metric.isOpen_ball⟩
  have hSn : Nonempty S := by
    let z : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r := ⟨q.val.symm ((0 : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),
      ⟨((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ⟨0, by simpa using hr⟩, rfl⟩⟩
    exact ⟨mobiusDiscRangeProjection D _ hND z⟩
  have hTn : Nonempty T := by
    refine ⟨⟨0, mem_ball_zero_iff.mpr ?_⟩⟩
    simpa only [norm_zero] using (pow_pos hr (Nat.card
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K)))
  exact ((S.openPartialHomeomorphSubtypeCoe hSn).symm.trans
    (mobiusDiscQuotientBranchHomeomorph D K q hi hz r hr hND hKG hsep).toOpenPartialHomeomorph).trans
      (T.openPartialHomeomorphSubtypeCoe hTn)

theorem mobiusDiscQuotientBranchChart_source {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (K : Subgroup
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite K]
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hi :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K ≤
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K, f.val (0 :
      ℂ) = (0 : ℂ))
    (r : ℝ) (hr : 0 < r) (hND : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r ⊆
      D.carrier) (hKG : K ≤ G)
    (hsep : ∀ g ∈ G, g ∉ K → Disjoint (g.val ''
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r)
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r)) :
    (mobiusDiscQuotientBranchChart D K q hi hz r hr hND hKG hsep).source =
      mobiusDiscQuotientImage D (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) hND := by
  simp [mobiusDiscQuotientBranchChart]

theorem mobiusDiscQuotientBranchChart_target {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (K : Subgroup
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite K]
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hi :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K ≤
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K, f.val (0 :
      ℂ) = (0 : ℂ))
    (r : ℝ) (hr : 0 < r) (hND : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r ⊆
      D.carrier) (hKG : K ≤ G)
    (hsep : ∀ g ∈ G, g ∉ K → Disjoint (g.val ''
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r)
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r)) :
    (mobiusDiscQuotientBranchChart D K q hi hz r hr hND hKG hsep).target =
      Metric.ball (0 : ℂ) (r ^ Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K)) := by
  simp [mobiusDiscQuotientBranchChart]

theorem mobiusDiscQuotientBranchChart_apply_projection {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (K : Subgroup
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite K]
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hi :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K ≤
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K, f.val (0 :
      ℂ) = (0 : ℂ))
    (r : ℝ) (hr : 0 < r) (hND : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r ⊆
      D.carrier) (hKG : K ≤ G)
    (hsep : ∀ g ∈ G, g ∉ K → Disjoint (g.val ''
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r)
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r))
    (z : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) :
    mobiusDiscQuotientBranchChart D K q hi hz r hr hND hKG hsep
      (mobiusDiscDomainProjection D (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) hND
        z) =
      (mobiusNormalizedDiscHomeomorph q r z).val ^ Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K) := by
  let S : TopologicalSpace.Opens (MobiusDomainQuotient D) :=
    ⟨mobiusDiscQuotientImage D (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) hND,
      mobiusDiscQuotientImage_isOpen D _ hND (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc_isComplexOpenDisc q hr).isOpen⟩
  have hSn : Nonempty S := ⟨mobiusDiscRangeProjection D _ hND z⟩
  have hsub := (S.openPartialHomeomorphSubtypeCoe hSn).left_inv
    (Set.mem_univ (mobiusDiscRangeProjection D _ hND z))
  change (S.openPartialHomeomorphSubtypeCoe hSn).symm
    (mobiusDiscDomainProjection D (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) hND
      z) =
      mobiusDiscRangeProjection D (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q
        r) hND z at hsub
  change ((mobiusDiscQuotientBranchHomeomorph D K q hi hz r hr hND hKG hsep)
    ((S.openPartialHomeomorphSubtypeCoe hSn).symm
      (mobiusDiscDomainProjection D (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) hND
        z))).val = _
  rw [hsub]
  exact mobiusDiscQuotientBranchHomeomorph_apply_projection D K q hi hz r hr hND hKG hsep z

/-- The actual local finite stabilizer, normalizer, disc, and translate separation that define
a branched chart on the full orbit quotient. -/
structure MobiusQuotientChartData {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  MobiusInvariantDomain G) where
  stabilizer : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup
  finiteStabilizer : Finite stabilizer
  normalizer : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup
  fixInfty : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate normalizer stabilizer ≤ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer
  fixZero : ∀ f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate normalizer stabilizer, f.val (0 : ℂ) = (0 : ℂ)
  radius : ℝ
  radius_pos : 0 < radius
  disc_subset : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc normalizer radius ⊆ D.carrier
  stabilizer_le : stabilizer ≤ G
  separated : ∀ g ∈ G, g ∉ stabilizer → Disjoint
    (g.val '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc normalizer
      radius) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc normalizer radius)

namespace MobiusQuotientChartData

variable {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain G}

def disc (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData
  D) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc C.normalizer C.radius

def coordinate (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData
  D) : C.disc ≃ₜ Metric.ball (0 : ℂ) C.radius :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusNormalizedDiscHomeomorph C.normalizer C.radius

def degree (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D) : ℕ :=
  Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer
    C.stabilizer)

theorem degree_pos (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D) : 0 < C.degree := by
  let : Finite C.stabilizer := C.finiteStabilizer
  let e := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence C.normalizer C.stabilizer
  let : Finite (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer
    C.stabilizer) :=
    Finite.of_surjective e e.surjective
  exact Nat.card_pos

def chart (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D) : OpenPartialHomeomorph (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D) ℂ := by
  let : Finite C.stabilizer := C.finiteStabilizer
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscQuotientBranchChart D C.stabilizer C.normalizer C.fixInfty C.fixZero
    C.radius C.radius_pos C.disc_subset C.stabilizer_le C.separated

theorem chart_source (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D) :
    C.chart.source = _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscQuotientImage D C.disc C.disc_subset := by
  let : Finite C.stabilizer := C.finiteStabilizer
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscQuotientBranchChart_source D C.stabilizer C.normalizer C.fixInfty C.fixZero
    C.radius C.radius_pos C.disc_subset C.stabilizer_le C.separated

theorem chart_target (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D) :
    C.chart.target = Metric.ball (0 : ℂ) (C.radius ^ C.degree) := by
  let : Finite C.stabilizer := C.finiteStabilizer
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscQuotientBranchChart_target D C.stabilizer C.normalizer C.fixInfty C.fixZero
    C.radius C.radius_pos C.disc_subset C.stabilizer_le C.separated

theorem chart_apply_projection (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D) (z :
  C.disc) :
    C.chart (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscDomainProjection D C.disc C.disc_subset z) =
      (C.coordinate z).val ^ C.degree := by
  let : Finite C.stabilizer := C.finiteStabilizer
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscQuotientBranchChart_apply_projection D C.stabilizer C.normalizer C.fixInfty C.fixZero
    C.radius C.radius_pos C.disc_subset C.stabilizer_le C.separated z

theorem coordinate_coe (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D) (z : C.disc) :
    C.normalizer.val z.val = ((C.coordinate z).val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusNormalizedDiscHomeomorph_coe C.normalizer C.radius z

theorem coordinate_symm_coe (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D) (z :
  Metric.ball (0 : ℂ) C.radius) :
    (C.coordinate.symm z).val = C.normalizer.val.symm (z.val :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusNormalizedDiscHomeomorph_symm_coe C.normalizer C.radius z

end MobiusQuotientChartData

/-- Every point of the genuine quotient is covered by a branch chart obtained from the
compact-set discontinuity hypothesis, without imposing freeness. -/
theorem mobiusQuotientChartData_cover {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G
      D.carrier)
    (p : MobiusDomainQuotient D) : ∃ C : MobiusQuotientChartData D, p ∈ C.chart.source := by
  obtain ⟨z, rfl⟩ := mobiusDomainProjection_surjective D p
  obtain ⟨q, r, hr, hqz, _hd, hzN, hcl, hrot, hsep⟩ :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_discontinuous_roundDisc G D.carrier D.isOpen D.invariant hD z.val z.property
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer G z.val
  have hfin : Finite K := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer_finite G hD
    z.val z.property).to_subtype
  have hi : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K ≤ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer := by
    intro f hf
    obtain ⟨a, _, rfl⟩ := hrot f hf
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty a
  have hz : ∀ f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K, f.val (0 : ℂ) = (0 : ℂ) := by
    intro f hf
    obtain ⟨a, _, rfl⟩ := hrot f hf
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero a
  have hND : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r ⊆ D.carrier := subset_closure.trans hcl
  have hKG : K ≤ G := fun f hf => ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer G
    z.val f).mp hf).1
  have hseparated : ∀ g ∈ G, g ∉ K →
      Disjoint (g.val '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) := by
    intro g hg hn
    apply (hsep ⟨g, hg⟩).2
    intro hfix
    exact hn ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer G z.val g).mpr ⟨hg,
      hfix⟩)
  let C : MobiusQuotientChartData D :=
    ⟨K, hfin, q, hi, hz, r, hr, hND, hKG, hseparated⟩
  refine ⟨C, ?_⟩
  rw [C.chart_source]
  refine ⟨⟨z.val, hzN⟩, ?_⟩
  rfl



/-- Analyticity descends through a genuine finite power branch. Continuity at the branch value
is sufficient; a nonzero derivative at the branched point is not assumed. -/
theorem analyticAt_of_comp_power (n : ℕ) (hn : n ≠ 0) (f : ℂ → ℂ) (z : ℂ)
    (hc : ContinuousAt f (z ^ n)) (ha : AnalyticAt ℂ (fun w : ℂ => f (w ^ n)) z) :
    AnalyticAt ℂ f (z ^ n) := by
  let : NeZero n := ⟨hn⟩
  have descend (w : ℂ) (hw : w ≠ 0)
      (h : AnalyticAt ℂ (fun v : ℂ => f (v ^ n)) w) : AnalyticAt ℂ f (w ^ n) := by
    have hd : deriv (fun v : ℂ => v ^ n) w ≠ 0 := by
      rw [deriv_pow_field]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr hn) (pow_ne_zero _ hw)
    exact (analyticAt_comp_iff_of_deriv_ne_zero (analyticAt_id.pow n) hd).mp h
  by_cases hz : z = 0
  · subst z
    rw [zero_pow hn] at hc ⊢
    let U : Set ℂ := {w | AnalyticAt ℂ (fun v : ℂ => f (v ^ n)) w}
    have hU : IsOpen U := isOpen_analyticAt ℂ _
    have hW : (fun w : ℂ => w ^ n) '' U ∈ 𝓝 (0 : ℂ) := by
      apply ((Complex.isOpenQuotientMap_pow n).isOpenMap U hU).mem_nhds
      exact ⟨0, ha, zero_pow hn⟩
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hc
    have hWp : ∀ᶠ y in 𝓝[≠] (0 : ℂ), y ∈ (fun w : ℂ => w ^ n) '' U :=
      mem_nhdsWithin_of_mem_nhds hW
    filter_upwards [hWp, self_mem_nhdsWithin] with y hy hy0
    obtain ⟨w, hw, hwy⟩ := hy
    have hw0 : w ≠ 0 := by
      intro hw0
      apply hy0
      change y = 0
      simpa only [hw0, zero_pow hn] using hwy.symm
    rw [← hwy]
    exact (descend w hw0 hw).differentiableAt
  · exact descend z hz ha

/-- At every point of an open target, analytic power pullbacks and continuity characterize
analyticity of the descended coordinate, including the ramified value. -/
theorem analyticOnNhd_of_comp_power (n : ℕ) (hn : n ≠ 0) (f : ℂ → ℂ) (S : Set ℂ)
    (hc : ContinuousOn f S)
    (ha : AnalyticOnNhd ℂ (fun w : ℂ => f (w ^ n)) ((fun w : ℂ => w ^ n) ⁻¹' S))
    (hS : IsOpen S) : AnalyticOnNhd ℂ f S := by
  let : NeZero n := ⟨hn⟩
  intro z hz
  obtain ⟨w, rfl⟩ := (Complex.isOpenQuotientMap_pow n).surjective z
  exact analyticAt_of_comp_power n hn f w
    ((hc _ hz).continuousAt (hS.mem_nhds hz)) (ha w hz)


open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces


/-- The actual Mobius action on an invariant sphere domain is analytic for the inherited complex structure. -/
theorem mobiusDomain_action_analytic {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain H) (g : H) :
    RiemannAnalyticMap (mobiusDomainRiemannSurface D).toRiemannAtlas
      (mobiusDomainRiemannSurface D).toRiemannAtlas (fun z : D.carrier => g • z) := by
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.liftLocalHomeomorph Subtype.val Subtype.val
    D.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    D.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    g.val.val (fun z : D.carrier => g • z) (mobius_riemannSphere_analytic g.val)
    (continuous_const_smul g) (fun _ => rfl)


/-- Genuine orbit-quotient power charts have analytic transitions, including branch values.
The lift of each transition is an actual Mobius transformation followed by a power map. -/
theorem mobius_power_quotient_charts_compatible {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (q₁ q₂ : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (r₁ r₂ : ℝ)
    (hr₂ : 0 < r₂) (n₁ n₂ : ℕ) (hn₁ : n₁ ≠ 0)
    (hD₁ : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q₁ r₁ ⊆ D.carrier)
    (hD₂ : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q₂ r₂ ⊆ D.carrier)
    (e f : OpenPartialHomeomorph (MobiusDomainQuotient D) ℂ)
    (heS : e.source = Set.range (fun a : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q₁
      r₁ =>
      mobiusDomainProjection D ⟨a.val, hD₁ a.property⟩))
    (hfS : f.source = Set.range (fun b : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q₂
      r₂ =>
      mobiusDomainProjection D ⟨b.val, hD₂ b.property⟩))
    (heP : ∀ a : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q₁ r₁,
      e (mobiusDomainProjection D ⟨a.val, hD₁ a.property⟩) =
        sphereFiniteChart (q₁.val a.val) ^ n₁)
    (hfP : ∀ b : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q₂ r₂,
      f (mobiusDomainProjection D ⟨b.val, hD₂ b.property⟩) =
        sphereFiniteChart (q₂.val b.val) ^ n₂) :
    AnalyticOnNhd ℂ (e.symm.trans f) (e.symm.trans f).source := by
  intro w hw
  obtain ⟨a, ha⟩ := heS ▸ e.map_target hw.1
  obtain ⟨b, hb⟩ := hfS ▸ hw.2
  change mobiusDomainProjection D ⟨a.val, hD₁ a.property⟩ = e.symm w at ha
  change mobiusDomainProjection D ⟨b.val, hD₂ b.property⟩ = e.symm w at hb
  obtain ⟨u, hu, hqu⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusNormalizedDisc q₁ r₁
    a.val).mp a.property
  let T : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := fun v => q₁.val.symm (v :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  have hT : Continuous T := (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
    q₁).symm.continuous.comp OnePoint.continuous_coe
  have hTu : T u = a.val := q₁.val.injective (by simpa only [T, Equiv.apply_symm_apply] using hqu)
  have huw : u ^ n₁ = w := by
    rw [← sphereFiniteChart_coe u, hqu, ← heP a, ha, e.right_inv hw.1]
  obtain ⟨g, hg⟩ := Quotient.exact (hb.trans ha.symm)
  have hga : g.val.val a.val = b.val := congrArg Subtype.val hg
  let M : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup := q₂ * g.val * q₁⁻¹
  have hM : M.val (u : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = q₂.val b.val := by
    change q₂.val (g.val.val (T u)) = q₂.val b.val
    rw [hTu, hga]
  have hbfin : q₂.val b.val ≠ ∞ := by
    obtain ⟨v, _hv, hqv⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusNormalizedDisc q₂ r₂
      b.val).mp b.property
    rw [← hqv]
    exact OnePoint.coe_ne_infty _
  have hMa : AnalyticAt ℂ (fun v : ℂ => sphereFiniteChart (M.val (v : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))) u := by
    apply mobius_finite_chart_analytic M u
    refine ⟨by rw [sphereFiniteChart_target]; trivial, ?_⟩
    change M.val (sphereFiniteChart.symm u) ∈ sphereFiniteChart.source
    rw [sphereFiniteChart_symm, sphereFiniteChart_source]
    exact (hM.trans_ne hbfin)
  have hnear₁ : ∀ᶠ v in 𝓝 u, v ∈ Metric.ball (0 : ℂ) r₁ := Metric.isOpen_ball.mem_nhds hu
  have hnear₂ : ∀ᶠ v in 𝓝 u, g.val.val (T v) ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q₂ r₂ := by
    have hc : Continuous (fun v : ℂ => g.val.val (T
      v)) := (_root_.LowDimensionalTopology.Geometry.Mobius.continuous_mobiusBoundary g.val).comp hT
    apply hc.continuousAt.eventually
    apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc_isComplexOpenDisc q₂
      hr₂).isOpen.mem_nhds
    change g.val.val (T u) ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q₂ r₂
    rw [hTu, hga]
    exact b.property
  have hagree : (fun v : ℂ => sphereFiniteChart (M.val (v :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ^ n₂) =ᶠ[𝓝 u]
      (fun v : ℂ => (e.symm.trans f) (v ^ n₁)) := by
    filter_upwards [hnear₁, hnear₂] with v hv₁ hv₂
    have hvN : T v ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q₁ r₁ := by
      exact ⟨(v : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ⟨v, hv₁, rfl⟩, rfl⟩
    let a' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q₁ r₁ := ⟨T v, hvN⟩
    let b' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q₂ r₂ := ⟨g.val.val (T v), hv₂⟩
    let x : D.carrier := ⟨a'.val, hD₁ a'.property⟩
    let y : D.carrier := ⟨b'.val, hD₂ b'.property⟩
    have hxy : mobiusDomainProjection D y = mobiusDomainProjection D x := by
      have he : y = g • x := rfl
      rw [he, mobiusDomainProjection_smul]
    have hx : mobiusDomainProjection D x ∈ e.source := by
      rw [heS]
      exact ⟨a', rfl⟩
    have hep : e (mobiusDomainProjection D x) = v ^ n₁ := by
      rw [heP a']
      change sphereFiniteChart (q₁.val (q₁.val.symm (v :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))) ^ n₁ = _
      rw [Equiv.apply_symm_apply, sphereFiniteChart_coe]
    have hei : e.symm (v ^ n₁) = mobiusDomainProjection D x := by
      rw [← hep, e.left_inv hx]
    change sphereFiniteChart (M.val (v :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ^ n₂ = f (e.symm (v ^ n₁))
    rw [hei, ← hxy, hfP b']
    rfl
  have hacomp : AnalyticAt ℂ (fun v : ℂ => (e.symm.trans f) (v ^ n₁)) u :=
    (hMa.pow n₂).congr hagree
  have hc : ContinuousAt (e.symm.trans f) (u ^ n₁) := by
    rw [huw]
    exact (e.symm.trans f).continuousAt hw
  simpa only [huw] using analyticAt_of_comp_power n₁ hn₁ (e.symm.trans f) u hc hacomp


/-- The actual full-group branched chart family has analytic overlaps, even when either chart
is centered at an elliptic fixed orbit. -/
theorem MobiusQuotientChartData.compatible {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (C E : MobiusQuotientChartData D) :
    AnalyticOnNhd ℂ (C.chart.symm.trans E.chart) (C.chart.symm.trans E.chart).source := by
  apply mobius_power_quotient_charts_compatible D C.normalizer E.normalizer C.radius E.radius
    E.radius_pos C.degree E.degree C.degree_pos.ne' C.disc_subset E.disc_subset
    C.chart E.chart C.chart_source E.chart_source
  · intro a
    have hp := C.chart_apply_projection a
    have hc : sphereFiniteChart (C.normalizer.val a.val) = (C.coordinate a).val := by
      simpa only [sphereFiniteChart_coe] using congrArg sphereFiniteChart (C.coordinate_coe a)
    exact hp.trans (congrArg (fun z : ℂ => z ^ C.degree) hc.symm)
  · intro b
    have hp := E.chart_apply_projection b
    have hc : sphereFiniteChart (E.normalizer.val b.val) = (E.coordinate b).val := by
      simpa only [sphereFiniteChart_coe] using congrArg sphereFiniteChart (E.coordinate_coe b)
    exact hp.trans (congrArg (fun z : ℂ => z ^ E.degree) hc.symm)

/-- The original quotient topology carries the genuine branched complex atlas supplied by
its finite cyclic stabilizers. -/
def mobiusQuotientRiemannAtlas {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G
      D.carrier) :
    RiemannAtlas (MobiusDomainQuotient D) where
  charts := Set.range (fun C : MobiusQuotientChartData D => C.chart)
  cover p := by
    obtain ⟨C, hp⟩ := mobiusQuotientChartData_cover D hD p
    exact ⟨C.chart, ⟨C, rfl⟩, hp⟩
  compatible e he f hf := by
    obtain ⟨C, rfl⟩ := he
    obtain ⟨E, rfl⟩ := hf
    exact C.compatible E

/--
A discontinuous actual Mobius action on any connected open sphere
domain yields a Riemann surface on the actual orbit quotient, with elliptic branching included.
-/
def mobiusQuotientRiemannSurface {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G
      D.carrier) :
    RiemannSurface (MobiusDomainQuotient D) where
  toRiemannAtlas := mobiusQuotientRiemannAtlas D hD
  t2Space := mobiusDomainQuotient_t2 D hD
  connectedSpace := mobiusDomainQuotient_connected D

theorem quotient_admits_riemannSurface_of_discontinuous_action {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G
      D.carrier) :
    Nonempty (RiemannSurface (MobiusDomainQuotient D)) :=
  ⟨mobiusQuotientRiemannSurface D hD⟩

namespace MobiusQuotientChartData

variable {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain G}

theorem degree_eq_stabilizer_card (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData
  D) : C.degree = Nat.card C.stabilizer :=
  (Nat.card_congr (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
    C.normalizer C.stabilizer).toEquiv).symm

theorem disc_isOpen (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D) : IsOpen C.disc :=
  (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc_isComplexOpenDisc C.normalizer
    C.radius_pos).isOpen

theorem projection_mem_source (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D) (z :
  C.disc) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscDomainProjection D C.disc C.disc_subset z ∈ C.chart.source := by
  rw [C.chart_source]
  exact ⟨z, rfl⟩

theorem pow_mem_target (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D) (u : Metric.ball
  (0 : ℂ) C.radius) :
    u.val ^ C.degree ∈ C.chart.target := by
  rw [C.chart_target]
  exact (_root_.LowDimensionalTopology.Geometry.Surfaces.complexDiscPower C.degree C.degree_pos.ne' C.radius
    C.radius_pos.le u).property

/-- Pulling the inverse branch chart back by the power map gives the original quotient projection
of the genuine inverse Mobius coordinate, even at the center. -/
theorem chart_symm_pow (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D) (u : Metric.ball
  (0 : ℂ) C.radius) :
    C.chart.symm (u.val ^ C.degree) =
      _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscDomainProjection D C.disc C.disc_subset (C.coordinate.symm u) := by
  have hleft := C.chart.left_inv (C.projection_mem_source (C.coordinate.symm u))
  rw [C.chart_apply_projection, Homeomorph.apply_symm_apply] at hleft
  exact hleft

end MobiusQuotientChartData


/-- The actual open unit disc as a connected invariant domain of the Riemann sphere. -/
def unitDiscMobiusInvariantDomain (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    MobiusInvariantDomain H where
  carrier := _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
  isOpen := _root_.LowDimensionalTopology.Geometry.Mobius.isOpen_extendedUnitDisc
  isConnected := _root_.LowDimensionalTopology.Geometry.Mobius.isConnected_extendedUnitDisc
  invariant := hInv

/--
A surface is of hyperbolic type when its actual complex structure is
conformally equivalent to a discontinuous no-elliptic unit-disc quotient.
-/
def IsHyperbolicType {X : Type*} [TopologicalSpace X] (R : RiemannSurface X) : Prop :=
  ∃ (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc),
    (∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) ∧
    RiemannConformallyEquivalent R
      (mobiusQuotientRiemannSurface (unitDiscMobiusInvariantDomain H hInv) hD)

/-- The source real-manifold generalization replaces complex coordinate space by real
Euclidean n-space and retains connectedness and the Hausdorff condition. No differentiable
transition requirement is imposed for the purely topological version. -/
structure ConnectedHausdorffRealManifold (n : ℕ) (X : Type*) [TopologicalSpace X] where
  chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin n)) X
  t2Space : T2Space X
  connectedSpace : ConnectedSpace X

end LowDimensionalTopology.Geometry.Surfaces
