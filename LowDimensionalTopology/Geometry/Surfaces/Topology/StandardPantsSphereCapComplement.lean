module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.StandardPantsSphereCapRanges

/-!
# The literal pants region as the complement of three full closed spherical caps

This construction has no surface-classification hypothesis. The norm bounds
separate the explicit closed ranges, and finite sphere coordinates identify
their complement with the existing standard open planar pants region.
-/

@[expose] public section
noncomputable section
open Set
open scoped OnePoint

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Mobius

theorem pantsStandardExtendedCap_pairwise_disjoint :
    Pairwise fun i j : Fin 3 => Disjoint (pantsStandardExtendedCap i) (pantsStandardExtendedCap j) := by
  intro i j hij
  apply disjoint_left.mpr
  intro p hpi hpj
  induction p using OnePoint.rec with
  | infty =>
    fin_cases i <;> fin_cases j
    all_goals try exact (hij rfl).elim
    all_goals simp [pantsStandardExtendedCap] at hpi hpj
  | coe z =>
    obtain ⟨h₀, h₁, h₂⟩ := pantsModel_norm_separation z
    fin_cases i <;> fin_cases j
    all_goals try exact (hij rfl).elim
    all_goals simp [pantsStandardExtendedCap] at hpi hpj
    all_goals linarith

/-- The three actual full closed sphere-cap ranges are pairwise disjoint. -/
theorem pantsStandardSphereCap_pairwise_disjoint : Pairwise fun i j : Fin 3 =>
    Disjoint (range (pantsStandardSphereCap i)) (range (pantsStandardSphereCap j)) := by
  intro i j hij
  rw [pantsStandardSphereCap_range, pantsStandardSphereCap_range]
  exact (disjoint_image_iff pantsComplexSphereHomeomorph.injective).mpr
    (pantsStandardExtendedCap_pairwise_disjoint hij)

/-- Removing the full closed extended caps gives precisely the literal P0. -/
theorem pantsStandardExtendedCaps_compl :
    (⋃ i : Fin 3, pantsStandardExtendedCap i)ᶜ = (↑) '' pantsPlanarRegion := by
  ext p
  induction p using OnePoint.rec with
  | infty => simp [pantsStandardExtendedCap, Fin.forall_fin_succ]
  | coe z => simp [pantsStandardExtendedCap, pantsPlanarRegion, Fin.forall_fin_succ]

/-- The exact same complement equality in the real three-dimensional sphere. -/
theorem pantsStandardSphereCaps_compl :
    (⋃ i : Fin 3, range (pantsStandardSphereCap i))ᶜ =
      pantsComplexSphereHomeomorph '' ((↑) '' pantsPlanarRegion) := by
  have hUnion : (⋃ i : Fin 3, range (pantsStandardSphereCap i)) =
      pantsComplexSphereHomeomorph '' (⋃ i : Fin 3, pantsStandardExtendedCap i) := by
    simp_rw [pantsStandardSphereCap_range]
    exact image_iUnion.symm
  rw [hUnion, ← pantsComplexSphereHomeomorph.image_compl, pantsStandardExtendedCaps_compl]

/-- The complement of these actual three full closed cap ranges is homeomorphic
to the existing radius-two planar region with two closed radius-one-half holes. -/
def pantsStandardSphereComplementHomeomorph :
    ↥((⋃ i : Fin 3, range (pantsStandardSphereCap i))ᶜ) ≃ₜ pantsPlanarRegion := by
  let j : ℂ → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun z => pantsComplexSphereHomeomorph (z : ExtendedComplex)
  have hj : Topology.IsEmbedding j :=
    pantsComplexSphereHomeomorph.isEmbedding.comp OnePoint.isOpenEmbedding_coe.isEmbedding
  have hJ : j '' pantsPlanarRegion = (⋃ i : Fin 3, range (pantsStandardSphereCap i))ᶜ := by
    simpa only [j, image_image] using pantsStandardSphereCaps_compl.symm
  exact ((hj.homeomorphImage pantsPlanarRegion).trans (Homeomorph.setCongr hJ)).symm

end LowDimensionalTopology.Geometry.Surfaces
