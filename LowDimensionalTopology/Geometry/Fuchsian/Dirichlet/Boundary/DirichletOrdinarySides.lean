module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonIdealBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianLimitSets
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic.Linarith
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Topology
open scoped OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual disc equidistance equation has a polynomial form continuous
through the genuine closed disc, so no boundary distance is invented. -/
theorem disc_equidistant_weighted_norm_identity (x w p : 𝔻)
    (h : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist x w =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist x p) :
    (1-‖(p:ℂ)‖^2)*‖(x:ℂ)-(w:ℂ)‖^2 =
      (1-‖(w:ℂ)‖^2)*‖(x:ℂ)-(p:ℂ)‖^2 := by
  have hc := congrArg Real.cosh h
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_cosh_distance,_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_cosh_distance] at hc
  have hx : 1-‖(x:ℂ)‖^2 ≠ 0 := (sub_pos.mpr x.sq_norm_lt_one).ne'
  have hw : 1-‖(w:ℂ)‖^2 ≠ 0 := (sub_pos.mpr w.sq_norm_lt_one).ne'
  have hp : 1-‖(p:ℂ)‖^2 ≠ 0 := (sub_pos.mpr p.sq_norm_lt_one).ne'
  have he :
      2*‖(x:ℂ)-(w:ℂ)‖^2/((1-‖(x:ℂ)‖^2)*(1-‖(w:ℂ)‖^2)) =
      2*‖(x:ℂ)-(p:ℂ)‖^2/((1-‖(x:ℂ)‖^2)*(1-‖(p:ℂ)‖^2)) := by linarith
  rw [div_eq_div_iff (mul_ne_zero hx hw) (mul_ne_zero hx hp)] at he
  have hh : (1-‖(x:ℂ)‖^2) *
      (2*((1-‖(p:ℂ)‖^2)*‖(x:ℂ)-(w:ℂ)‖^2-
        (1-‖(w:ℂ)‖^2)*‖(x:ℂ)-(p:ℂ)‖^2)) = 0 := by
    nlinarith only [he]
  have hh' := (mul_eq_zero.mp hh).resolve_left hx
  linarith only [hh']

/-- If one endpoint of genuine equidistant pairs tends to an ideal point,
every simultaneous closed-disc limit of the bisector points is that same
actual ideal point. -/
theorem disc_equidistant_boundary_limit_eq
    (w : ℂ) (hw : ‖w‖ < 1) (x p : ℕ → ℂ) (α ζ : ℂ)
    (hx : Tendsto x atTop (𝓝 α)) (hp : Tendsto p atTop (𝓝 ζ)) (hζ : ‖ζ‖ = 1)
    (he : ∀ n, (1-‖p n‖^2)*‖x n-w‖^2 = (1-‖w‖^2)*‖x n-p n‖^2) :
    α = ζ := by
  have hl : Tendsto (fun n => (1-‖p n‖^2)*‖x n-w‖^2) atTop (𝓝 (0:ℝ)) := by
    have hh : Tendsto (fun n => (1-‖p n‖^2)*‖x n-w‖^2) atTop
        (𝓝 ((1-‖ζ‖^2)*‖α-w‖^2)) :=
      (tendsto_const_nhds.sub (hp.norm.pow 2)).mul ((hx.sub tendsto_const_nhds).norm.pow 2)
    simpa only [hζ,one_pow,sub_self,zero_mul] using hh
  have hr : Tendsto (fun n => (1-‖w‖^2)*‖x n-p n‖^2) atTop
      (𝓝 ((1-‖w‖^2)*‖α-ζ‖^2)) :=
    tendsto_const_nhds.mul ((hx.sub hp).norm.pow 2)
  have hr' : Tendsto (fun n => (1-‖p n‖^2)*‖x n-w‖^2) atTop
      (𝓝 ((1-‖w‖^2)*‖α-ζ‖^2)) := by
    convert hr using 1
    exact funext he
  have hzero := tendsto_nhds_unique hr' hl
  have hwpos : 0 < 1-‖w‖^2 := by nlinarith [norm_nonneg w]
  have hs : ‖α-ζ‖^2 = 0 := (mul_eq_zero.mp hzero).resolve_left hwpos.ne'
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))

/-- Actual Dirichlet bisectors have a finite label family on every closed
sphere subset avoiding the genuine limit set. This includes ordinary ideal
points; compactness is taken in the true sphere, not incorrectly in the open
native disc. -/
theorem dirichletBisectors_closed_sphere_off_limit_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (w : P.domain.carrier)
    (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hK : IsClosed K) (hKL : Disjoint K
      (fuchsianLimitSet H)) :
    {g : H | g ≠ 1 ∧ ∃ z ∈ dirichletBisector P w g, z.val ∈ K}.Finite := by
  classical
  by_contra hfin
  let labels : Set H := {g | g ≠ 1 ∧ ∃ z ∈ dirichletBisector P w g, z.val ∈ K}
  have hInf : labels.Infinite := hfin
  let e := hInf.natEmbedding labels
  let g : ℕ → H := fun n => (e n).val
  have hg : Function.Injective g := Subtype.val_injective.comp e.injective
  have hex (n : ℕ) : ∃ z ∈ dirichletBisector P w (g n), z.val ∈ K := (e n).property.2
  choose z hzbis hzK using hex
  let seq : ℕ → ℂ × ℂ := fun n =>
    ((P.finiteCoordinate (g n • w):ℂ),(P.finiteCoordinate (z n):ℂ))
  have hseq (n : ℕ) : seq n ∈ Metric.closedBall (0:ℂ) 1 ×ˢ Metric.closedBall (0:ℂ) 1 := by
    constructor
    · simpa only [Metric.mem_closedBall,dist_zero_right] using (P.finiteCoordinate (g n • w)).norm_lt_one.le
    · simpa only [Metric.mem_closedBall,dist_zero_right] using (P.finiteCoordinate (z n)).norm_lt_one.le
  obtain ⟨ab,_hab,φ,hφ,hlim⟩ :=
    ((isCompact_closedBall (0:ℂ) 1).prod (isCompact_closedBall (0:ℂ) 1)).tendsto_subseq hseq
  have hp : Tendsto (fun n => (P.finiteCoordinate (g (φ n) • w):ℂ)) atTop (𝓝 ab.1) :=
    continuous_fst.continuousAt.tendsto.comp hlim
  have hx : Tendsto (fun n => (P.finiteCoordinate (z (φ n)):ℂ)) atTop (𝓝 ab.2) :=
    continuous_snd.continuousAt.tendsto.comp hlim
  have horbit : Tendsto (fun n => g (φ n) • w.val) atTop (𝓝 (ab.1:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) := by
    convert OnePoint.continuous_coe.continuousAt.tendsto.comp hp using 1
    ext n
    exact (P.finiteCoordinate_extended (g (φ n) • w)).symm
  have hL : (ab.1:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ fuchsianLimitSet H := by
    rw [fuchsianLimitSet_eq_nonElementary H hNE]
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrbitLimitSet_subset_limitSet H hNE P.discrete w.val
      ⟨g ∘ φ,hg.comp hφ.injective,horbit⟩
  have hpNorm : ‖ab.1‖ = 1 := by
    have hh := P.asFuchsianDisc.limitSet_subset_frontier hL
    change (ab.1:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc at hh
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle] at hh
    simpa only [_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe,sub_zero] using hh
  have hab : ab.2 = ab.1 := disc_equidistant_boundary_limit_eq
    (P.finiteCoordinate w) (P.finiteCoordinate w).norm_lt_one _ _ ab.2 ab.1 hx hp hpNorm (by
      intro n
      apply disc_equidistant_weighted_norm_identity
      have hh := hzbis (φ n)
      change P.hyperbolicDist (z (φ n)) w = P.hyperbolicDist (z (φ n)) (g (φ n) • w) at hh
      rwa [P.hyperbolicDist_eq_discPathDist,P.hyperbolicDist_eq_discPathDist] at hh)
  have hxSphere : Tendsto (fun n => (z (φ n)).val) atTop (𝓝 (ab.2:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) := by
    convert OnePoint.continuous_coe.continuousAt.tendsto.comp hx using 1
    ext n
    exact (P.finiteCoordinate_extended (z (φ n))).symm
  have habK : (ab.2:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ K :=
    hK.mem_of_tendsto hxSphere (Eventually.of_forall (fun n => hzK (φ n)))
  rw [hab] at habK
  exact Set.disjoint_left.mp hKL habK hL

/-- The true side sets, rather than merely their bisector witnesses, form a
finite family on any actual closed sphere region disjoint from the limit set. -/
theorem dirichletSides_closed_sphere_off_limit_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (w : P.domain.carrier)
    (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hK : IsClosed K) (hKL : Disjoint K
      (fuchsianLimitSet H)) :
    {S : Set P.domain.carrier | IsFuchsianPolygonSide P (dirichletDomain P w) S ∧
      ∃ z ∈ S, z.val ∈ K}.Finite := by
  apply ((dirichletBisectors_closed_sphere_off_limit_finite P hNE w K hK hKL).image
    (fun g : H => closure (dirichletDomain P w) ∩
      fuchsianDomainTile P (dirichletDomain P w) g)).subset
  rintro S ⟨⟨⟨g,hg,rfl⟩,_hS⟩,z,hzS,hzK⟩
  exact ⟨g,⟨hg,z,dirichlet_closedTile_intersection_subset_bisector P w g hzS,hzK⟩,rfl⟩

/-- Every actual ordinary sphere point has a genuine open neighbourhood whose
closed neighbourhood meets only finitely many true Dirichlet sides. It applies
at ideal boundary points as well as at native interior points. -/
theorem dirichletSides_ordinary_neighborhood_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (w : P.domain.carrier)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hξ : ξ ∉ fuchsianLimitSet H) :
    ∃ U : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, IsOpen U ∧ ξ ∈ U ∧
      Disjoint (closure U) (fuchsianLimitSet H) ∧
      {S : Set P.domain.carrier | IsFuchsianPolygonSide P (dirichletDomain P w) S ∧
        ∃ z ∈ S, z.val ∈ closure U}.Finite := by
  have hLc : IsClosed (fuchsianLimitSet H) := isClosed_closure
  obtain ⟨K,hKnh,hKc,hKsub⟩ :=
    exists_mem_nhds_isClosed_subset (hLc.isOpen_compl.mem_nhds hξ)
  let U := interior K
  have hξU : ξ ∈ U := mem_interior_iff_mem_nhds.mpr hKnh
  have hclsub : closure U ⊆ K := closure_minimal interior_subset hKc
  have hdis : Disjoint (closure U) (fuchsianLimitSet H) :=
    Set.disjoint_left.mpr (fun _ hz hL => hKsub (hclsub hz) hL)
  exact ⟨U,isOpen_interior,hξU,hdis,
    dirichletSides_closed_sphere_off_limit_finite P hNE w (closure U) isClosed_closure hdis⟩

end LowDimensionalTopology.Geometry.Fuchsian
