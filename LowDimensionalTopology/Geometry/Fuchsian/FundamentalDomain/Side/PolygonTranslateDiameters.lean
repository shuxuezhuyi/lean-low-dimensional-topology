/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSides
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Klein.Closed
public import Mathlib.Analysis.Convex.StrictConvexSpace
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology Filter
open scoped Pointwise Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Surfaces

/-- Only finitely many actual closed polygon translates contain two disc points a fixed positive Euclidean distance apart. -/
theorem IsConvexFuchsianPolygon.euclidean_separated_tiles_finite
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (ε : ℝ) (hε : 0 < ε) :
    {g : H | ∃ a ∈ fuchsianDomainTile P D g, ∃ b ∈ fuchsianDomainTile P D g,
      ε ≤ dist (P.finiteCoordinate a : ℂ) (P.finiteCoordinate b : ℂ)}.Finite := by
  let S : Set (𝕔𝔻 × 𝕔𝔻) := {p | ε ≤ dist (p.1 : ℂ) (p.2 : ℂ)}
  let midpoint : 𝕔𝔻 × 𝕔𝔻 → ℂ := fun p =>
    (1 / 2 : ℝ) • _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p.1 + (1 / 2 : ℝ) • _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p.2
  have hco : Continuous (fun z : 𝕔𝔻 => (z : ℂ)) := Complex.UnitClosedDisc.continuous_coe
  have hS : IsCompact S := (isClosed_le continuous_const
    ((hco.comp continuous_fst).dist (hco.comp continuous_snd))).isCompact
  have hmid : Continuous midpoint := by
    have hcc : Continuous _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate := _root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.continuous
    dsimp [midpoint]
    exact ((hcc.comp continuous_fst).const_smul (1 / 2 : ℝ)).add
      ((hcc.comp continuous_snd).const_smul (1 / 2 : ℝ))
  let K := midpoint '' S
  have hK : IsCompact K := hS.image hmid
  have hKball : K ⊆ Metric.ball (0 : ℂ) 1 := by
    rintro _ ⟨p,hp,rfl⟩
    have hpne : p.1 ≠ p.2 := by
      intro he
      have he' : (p.1 : ℂ) = (p.2 : ℂ) := congrArg (fun z : 𝕔𝔻 => (z : ℂ)) he
      have hh : ε ≤ dist (p.1 : ℂ) (p.2 : ℂ) := hp
      rw [he',dist_self] at hh
      exact hε.not_ge hh
    exact combo_mem_ball_of_ne
      (mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein p.1).norm_le_one)
      (mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein p.2).norm_le_one)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hpne) (by norm_num) (by norm_num) (by norm_num)
  have hFrange : range P.kleinCoordinate = Metric.ball (0 : ℂ) 1 := by
    change range (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ∘ P.finiteCoordinate) = _
    rw [range_comp,P.finiteCoordinate.surjective.range_eq,
      image_univ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
  have hKrange : K ⊆ range P.kleinCoordinate := by rwa [hFrange]
  have hpre : IsCompact (P.kleinCoordinate ⁻¹' K) :=
    P.kleinCoordinate_isOpenEmbedding.isEmbedding.isInducing.isCompact_preimage' hK hKrange
  apply (hD.locallyFinite.compact_hits_finite _ hpre).subset
  rintro g ⟨a,ha,b,hb,hab⟩
  have hgc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' fuchsianDomainTile P D g) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' (g • closure D))
    rw [P.discAction_image]
    exact hD.closure_convex.isometry_image (P.discAction_isometry g)
  have hc : Convex ℝ (P.kleinCoordinate '' fuchsianDomainTile P D g) := by
    change Convex ℝ ((fun x => _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (P.finiteCoordinate x)) '' _)
    rw [← image_image]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp hgc
  have hm : (1 / 2 : ℝ) • P.kleinCoordinate a + (1 / 2 : ℝ) • P.kleinCoordinate b ∈
      P.kleinCoordinate '' fuchsianDomainTile P D g :=
    hc ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩ (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨x,hx,hxm⟩ := hm
  refine ⟨x,hx,?_⟩
  change P.kleinCoordinate x ∈ K
  rw [hxm]
  exact ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate a),_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate b)),hab,rfl⟩

/-- Euclidean diameters of all distinct actual closed tiles tend to zero in the cofinite filter of the original group. -/
theorem IsConvexFuchsianPolygon.euclidean_closed_tile_diam_tendsto
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    Tendsto (fun g : H => Metric.diam
      ((fun x : P.domain.carrier => (P.finiteCoordinate x : ℂ)) '' fuchsianDomainTile P D g))
      cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hf := hD.euclidean_separated_tiles_finite (ε / 2) (by positivity)
  filter_upwards [hf.compl_mem_cofinite] with g hg
  have hdiam : Metric.diam
      ((fun x : P.domain.carrier => (P.finiteCoordinate x : ℂ)) '' fuchsianDomainTile P D g) ≤ ε / 2 := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
    exact (lt_of_not_ge (fun h => hg ⟨a,ha,b,hb,h⟩)).le
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg Metric.diam_nonneg]
  exact hdiam.trans_lt (by linarith)

/-- The same vanishing Euclidean diameters hold for the literal open polygon translates. -/
theorem IsConvexFuchsianPolygon.euclidean_polygon_translate_diam_tendsto
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    Tendsto (fun g : H => Metric.diam
      ((fun x : P.domain.carrier => (P.finiteCoordinate x : ℂ)) '' (g • D)))
      cofinite (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hD.euclidean_closed_tile_diam_tendsto (fun _ => Metric.diam_nonneg) (fun g => ?_)
  apply Metric.diam_mono (image_mono (Set.smul_set_mono subset_closure))
  apply (Metric.isBounded_ball (x := (0 : ℂ)) (r := 1)).subset
  rintro _ ⟨x,_hx,rfl⟩
  exact mem_ball_zero_iff.mpr (P.finiteCoordinate x).norm_lt_one

/-- property7: every sequence of distinct original group elements has vanishing Euclidean polygon diameters. -/
theorem IsConvexFuchsianPolygon.euclidean_polygon_translate_diam_sequence
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (g : ℕ → H) (hg : Function.Injective g) :
    Tendsto (fun j => Metric.diam
      ((fun x : P.domain.carrier => (P.finiteCoordinate x : ℂ)) '' (g j • D)))
      atTop (𝓝 0) := by
  have ht : Tendsto g cofinite cofinite := hg.tendsto_cofinite
  rw [Nat.cofinite_eq_atTop] at ht
  exact hD.euclidean_polygon_translate_diam_tendsto.comp ht

end LowDimensionalTopology.Geometry.Fuchsian
