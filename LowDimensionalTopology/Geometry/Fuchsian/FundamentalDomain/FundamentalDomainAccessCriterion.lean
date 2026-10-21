module
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.PlaneAccessibility

public import LowDimensionalTopology.External.LeanPool.Schoenflies.JordanClosed
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.IntermediateValue
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonGenerators
public import LowDimensionalTopology.Geometry.Polygon.Topology.Jordan.JordanPolygonRegions

/-!
# Accessible paired boundaries and local finiteness

Boundary mates and continuous access paths imply local finiteness for the
Fuchsian action. Taking the last boundary visit converts access curves to simple
arcs. Noncompact tiles use planar separation and a countable exceptional-set
argument; relatively compact tiles use proper discontinuity.
-/

@[expose] public section

noncomputable section

set_option maxHeartbeats 1000000

open Set Metric Schoenflies
open scoped Topology

open Topology

open Filter
open scoped Pointwise

namespace LowDimensionalTopology.Geometry.Fuchsian

open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon

/--
With the literal continuous-access hypothesis. No convexity or
polygonal accessibility is required, and elliptic stabilizers are allowed.
-/
theorem locallyFinite_of_frontier_mates_and_positive_access_paths {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier)
    (hD : IsFuchsianFundamentalDomain P D)
    (hmate : ∀ x ∈ frontier D, ∃ g : H, g ≠ 1 ∧ g • x ∈ frontier D)
    (haccess : ∀ x ∈ frontier D, ∃ γ : ℝ → P.domain.carrier,
      ContinuousOn γ (Icc 0 1) ∧ γ 0 = x ∧ ∀ t ∈ Ioc 0 1, γ t ∈ D) :
    IsLocallyFiniteFuchsianDomain P D := by
  classical
  let : Countable H := P.countable
  let : ContinuousConstSMul H P.domain.carrier := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainContinuousConstSMul P.domain
  have hDopen : IsOpen D := ((isFuchsianFundamentalDomain_iff P D).mp hD).1
  have hDconn : IsConnected D := ((isFuchsianFundamentalDomain_iff P D).mp hD).2.1
  by_cases hcompact : IsCompact (closure D)
  · apply (isLocallyFiniteFuchsianDomain_iff P D).mpr
    refine ⟨hD, ?_⟩
    let : ProperlyDiscontinuousSMul H P.domain.carrier :=
      _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomain_properlyDiscontinuous P.domain P.discontinuous
    intro x
    obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
    refine ⟨K, hxK, ?_⟩
    simpa only [fuchsianDomainTile, image_smul] using
      ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := H) hcompact hK
  let E : P.domain.carrier ≃ₜ Plane :=
    P.planeHomeomorph.trans _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanPlaneHomeomorph
  let V (g : H) : P.domain.carrier ≃ₜ Plane := (Homeomorph.smul g).trans E
  let U : H → Set Plane := fun g => V g '' D
  have hclosure : ∀ g, V g '' closure D = closure (U g) := fun g =>
    (V g).image_closure D
  have hopen : ∀ g, IsOpen (U g) := fun g => (V g).isOpenMap D hDopen
  have hconn : ∀ g, IsConnected (U g) := fun g =>
    hDconn.image (V g) (V g).continuous.continuousOn
  have hnc : ∀ g, ¬ IsCompact (closure (U g)) := by
    intro g hg
    apply hcompact
    apply (V g).isCompact_image.mp
    rwa [hclosure]
  have hdisj : ∀ i j, i ≠ j → Disjoint (U i) (closure (U j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨u, hu, huz⟩ hzj
    rw [← hclosure j] at hzj
    obtain ⟨v, hv, hvz⟩ := hzj
    have heq : i • u = j • v := by
      apply E.injective
      exact huz.trans hvz.symm
    have hne : j⁻¹ * i ≠ 1 := fun hh => hij (inv_mul_eq_one.mp hh).symm
    have hmul : (j⁻¹ * i) • u = v := by
      rw [mul_smul, heq, inv_smul_smul]
    exact Set.disjoint_left.mp (hD.disjoint_image_closure hne) ⟨u, hu, hmul⟩ hv
  have hcover : ∀ z : Plane, ∃ g : H, z ∈ closure (U g) := by
    intro z
    have hz : E.symm z ∈ ⋃ g : H, (fun x : P.domain.carrier => g • x) '' closure D := by
      rw [hD.closure_cover]
      trivial
    obtain ⟨g, u, hu, hgu⟩ := mem_iUnion.mp hz
    refine ⟨g, ?_⟩
    rw [← hclosure g]
    refine ⟨u, hu, ?_⟩
    change E (g • u) = z
    change g • u = E.symm z at hgu
    rw [hgu, E.apply_symm_apply]
  have haccess : ∀ i x, x ∈ frontier (U i) →
      ∃ p ∈ U i, ∃ A : Set Plane, IsArcBetween A x p ∧ A \ {x} ⊆ U i := by
    intro i x hx
    rw [← (V i).image_frontier D] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨γ, hc, h0, hinto⟩ := haccess y hy
    have hynot : y ∉ D := by
      rw [hDopen.frontier_eq] at hy
      exact hy.2
    have hxnot : V i y ∉ U i := by
      rintro ⟨w, hw, hwy⟩
      exact hynot ((V i).injective hwy ▸ hw)
    apply _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.continuous_boundary_access_simple_arc (hopen
      i) hxnot
      ((V i).continuous.comp_continuousOn hc) (congrArg (V i) h0)
    intro t ht
    exact ⟨γ t, hinto t ht, rfl⟩
  have hmateU : ∀ i x, x ∈ frontier (U i) →
      ∃ j, j ≠ i ∧ x ∈ frontier (U j) := by
    intro i x hx
    rw [← (V i).image_frontier D] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨g, hg, hgy⟩ := hmate y hy
    refine ⟨i * g⁻¹, ?_, ?_⟩
    · intro heq
      apply hg
      have hinv : g⁻¹ = 1 := by
        have h := congrArg (fun k : H => i⁻¹ * k) heq
        simpa only [inv_mul_cancel_left, inv_mul_cancel] using h
      exact inv_eq_one.mp hinv
    · rw [← (V (i * g⁻¹)).image_frontier D]
      refine ⟨g • y, hgy, ?_⟩
      change E ((i * g⁻¹) • (g • y)) = E (i • y)
      rw [mul_smul, inv_smul_smul]
  have hlf : LocallyFinite (fun i => closure (U i)) :=
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.locallyFinite_plane_tiles_of_access_boundary_mates U hopen hconn hnc hdisj hcover haccess hmateU
  have heq : ∀ i, E ⁻¹' closure (U i) = fuchsianDomainTile P D i := by
    intro i
    rw [← hclosure i]
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      exact ⟨y, hy, E.injective he⟩
    · rintro ⟨y, hy, hey⟩
      exact ⟨y, hy, congrArg E hey⟩
  apply (isLocallyFiniteFuchsianDomain_iff P D).mpr
  refine ⟨hD, ?_⟩
  simpa only [heq] using hlf.preimage_continuous E.continuous

/--
The original continuous-curve formulation. Revisits to the
boundary point are removed by taking its last visit, not by assuming a simple curve.
-/
theorem locallyFinite_of_frontier_mates_and_access_paths {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier)
    (hD : IsFuchsianFundamentalDomain P D)
    (hmate : ∀ x ∈ frontier D, ∃ g : H, g ≠ 1 ∧ g • x ∈ frontier D)
    (haccess : ∀ x ∈ frontier D, ∃ γ : ℝ → P.domain.carrier,
      ContinuousOn γ (Icc 0 1) ∧ γ 0 = x ∧ γ 1 ∈ D ∧ γ '' Icc 0 1 ⊆ D ∪ {x}) :
    IsLocallyFiniteFuchsianDomain P D := by
  apply locallyFinite_of_frontier_mates_and_positive_access_paths P D hD hmate
  intro x hx
  obtain ⟨γ, hc, h0, h1, himage⟩ := haccess x hx
  have hxnot : x ∉ D := by
    rw [((isFuchsianFundamentalDomain_iff P D).mp hD).1.frontier_eq] at hx
    exact hx.2
  let E : P.domain.carrier ≃ₜ Plane :=
    P.planeHomeomorph.trans _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanPlaneHomeomorph
  have hcont : ContinuousOn (fun t => E (γ t)) (Icc 0 1) :=
    E.continuous.comp_continuousOn hc
  obtain ⟨s, hs, _hs0, hsmem, hafter⟩ := exists_last_mem (C := {E x}) hcont isClosed_singleton
    zero_mem_I (by simp only [h0, mem_singleton_iff])
  have hγs : γ s = x := E.injective hsmem
  have hs1 : s ≠ 1 := by
    intro heq
    subst s
    exact hxnot (hγs ▸ h1)
  have hslt : s < 1 := lt_of_le_of_ne hs.2 hs1
  have hparam : MapsTo (reparam s 1) (Icc 0 1) (Icc 0 1) :=
    fun t ht => uIcc_subset_I hs one_mem_I (mapsTo_reparam ht)
  refine ⟨fun t => γ (reparam s 1 t), hc.comp continuous_reparam.continuousOn hparam,
    by simpa only [reparam_zero] using hγs, ?_⟩
  intro t ht
  have hu := hparam ⟨ht.1.le, ht.2⟩
  have hsu : s < reparam s 1 t := by
    dsimp only [reparam]
    nlinarith [mul_pos ht.1 (sub_pos.mpr hslt)]
  rcases himage ⟨reparam s 1 t, hu, rfl⟩ with hin | heq
  · exact hin
  · exact (hafter _ hu hsu (congrArg E heq)).elim

end LowDimensionalTopology.Geometry.Fuchsian
