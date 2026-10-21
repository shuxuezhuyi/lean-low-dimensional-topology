/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.Group
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The uniform topology of the actual general Möbius group

The supremum chordal distance is induced from continuous maps of the
compact chordal sphere. Compactness makes inverse maps uniformly continuous,
which proves continuity of inversion in this same metric.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}
local instance uniformChordalMetric : MetricSpace (ExtendedEuclidean n) := chordalMetricSpace n

def mobiusContinuousMap (f : GM n) : C(ExtendedEuclidean n,ExtendedEuclidean n) :=
  ⟨(f : ExtendedHomeomorph n),(f : ExtendedHomeomorph n).continuous⟩

theorem mobiusContinuousMap_injective : Function.Injective (mobiusContinuousMap (n := n)) := by
  intro f g h
  apply Subtype.ext
  apply Homeomorph.ext
  intro x
  exact congrArg (fun k : C(ExtendedEuclidean n,ExtendedEuclidean n) => k x) h

abbrev mobiusUniformMetricSpace (n : ℕ) : MetricSpace (GM n) :=
  MetricSpace.induced mobiusContinuousMap mobiusContinuousMap_injective inferInstance

local instance uniformMobiusMetric : MetricSpace (GM n) := mobiusUniformMetricSpace n

theorem mobiusContinuousMap_isometry : Isometry (mobiusContinuousMap (n := n)) :=
  MetricSpace.isometry_induced mobiusContinuousMap mobiusContinuousMap_injective

theorem mobius_uniform_dist_eq_iSup (f g : GM n) :
    dist f g = ⨆ x, chordalDist ((f : ExtendedHomeomorph n) x) ((g : ExtendedHomeomorph n) x) :=
  ContinuousMap.dist_eq_iSup

theorem mobius_tendsto_iff_tendstoUniformly {α : Type*} {p : Filter α}
    (F : α → GM n) (f : GM n) :
    Tendsto F p (𝓝 f) ↔
      TendstoUniformly (fun i x => (F i : ExtendedHomeomorph n) x)
        (fun x => (f : ExtendedHomeomorph n) x) p := by
  rw [mobiusContinuousMap_isometry.isEmbedding.isInducing.tendsto_nhds_iff]
  exact ContinuousMap.tendsto_iff_tendstoUniformly

theorem mobius_uniform_continuous_mul : Continuous (fun p : GM n × GM n => p.1 * p.2) := by
  apply mobiusContinuousMap_isometry.comp_continuous_iff.mp
  have h : Continuous (fun p : GM n × GM n =>
      ((mobiusContinuousMap p.2),(mobiusContinuousMap p.1))) :=
    (mobiusContinuousMap_isometry.continuous.comp continuous_snd).prodMk
      (mobiusContinuousMap_isometry.continuous.comp continuous_fst)
  exact ContinuousMap.continuous_comp'.comp h

theorem mobius_uniform_continuous_inv : Continuous (fun f : GM n => f⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro g
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have hu : UniformContinuous (fun x => (g : ExtendedHomeomorph n).symm x) :=
    CompactSpace.uniformContinuous_of_continuous (g : ExtendedHomeomorph n).symm.continuous
  obtain ⟨δ,hδ,hδprop⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  refine ⟨δ,hδ,?_⟩
  intro f hf
  change dist (mobiusContinuousMap f⁻¹) (mobiusContinuousMap g⁻¹) < ε
  apply ContinuousMap.dist_lt_iff_of_nonempty.mpr
  intro y
  change dist ((f : ExtendedHomeomorph n).symm y) ((g : ExtendedHomeomorph n).symm y) < ε
  have hpoint : dist ((f : ExtendedHomeomorph n) ((f : ExtendedHomeomorph n).symm y))
      ((g : ExtendedHomeomorph n) ((f : ExtendedHomeomorph n).symm y)) < δ :=
    (ContinuousMap.dist_apply_le_dist (f := mobiusContinuousMap f) (g := mobiusContinuousMap g)
      ((f : ExtendedHomeomorph n).symm y)).trans_lt hf
  have hh := hδprop hpoint
  simpa only [mobiusContinuousMap,Homeomorph.symm_apply_apply,Homeomorph.apply_symm_apply,dist_comm] using hh

instance mobius_isTopologicalGroup : IsTopologicalGroup (GM n) where
  continuous_mul := mobius_uniform_continuous_mul
  continuous_inv := mobius_uniform_continuous_inv

end LowDimensionalTopology.Geometry.Inversive
