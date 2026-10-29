module

public import LowDimensionalTopology.Unproved.Surfaces.HandleGroupPresentation
public import LowDimensionalTopology.Unproved.Surfaces.GenusComparison
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed
public import LowDimensionalTopology.Geometry.Surfaces.Topology.TorusFundamentalGroup
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Covering

/-!
# Transporting the handle presentation to the original closed surface

The sole outstanding mathematical input is the concrete based presentation of
the canonical handle model. Homeomorphism and change of basepoint transport it
to the actual underlying surface; its analytic structure is retained.
-/

@[expose] public section

noncomputable section

namespace LowDimensionalTopology.Geometry.Surfaces

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The zero-handle presentation is already proved: the actual two-sphere is
simply connected and the presentation with no generators is the trivial group. -/
theorem handleGroupPresentation_zero : Unproved.HandleGroupPresentation 0 := by
  let e : OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])
  let := riemannSphere_simplyConnected
  let : SimplyConnectedSpace (CanonicalHandleSurface 0) :=
    e.symm.toHomotopyEquiv.simplyConnectedSpace
  let : Subsingleton (LiZhongQC.surfaceGroup 0) :=
    (PresentedGroup.mk_surjective _).subsingleton
  let : Unique (FundamentalGroup (CanonicalHandleSurface 0) (canonicalHandleBasePoint 0)) :=
    uniqueOfSubsingleton 1
  let : Unique (LiZhongQC.surfaceGroup 0) := uniqueOfSubsingleton 1
  exact ⟨MulEquiv.ofUnique⟩

/-- A genuine homeomorphism to the handle model induces an isomorphism of
fundamental groups at the original point and the specified model point.
Path connectedness supplies the necessary change of basepoint. -/
def fundamentalGroupCanonicalHandleMulEquiv [PathConnectedSpace X] {g : ℕ}
    (e : X ≃ₜ CanonicalHandleSurface g) (x : X) :
    FundamentalGroup X x ≃*
      FundamentalGroup (CanonicalHandleSurface g) (canonicalHandleBasePoint g) := by
  let := e.pathConnectedSpace
  exact (fundamentalGroupHomeomorphMulEquiv e x).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
      (e x) (canonicalHandleBasePoint g))

/-- The canonical presentation, when established, transports to every
basepoint of every path-connected surface with this topological handle genus.
Compactness comes from the actual handle-model homeomorphism. -/
theorem sourceHasGenus_of_topologicalGenus [PathConnectedSpace X] {g : ℕ}
    (hgenus : HasTopologicalGenus X g)
    (hPresentation : Unproved.HandleGroupPresentation g) :
    LiZhongQC.HasGenus X g := by
  let := HandleSeparation.hasTopologicalGenus_compactSpace hgenus
  obtain ⟨e⟩ := hgenus
  refine ⟨inferInstance, fun x => ?_⟩
  exact ⟨(fundamentalGroupCanonicalHandleMulEquiv e x).trans
    (Classical.choice hPresentation)⟩

/-- At a specified point of a native closed Riemann surface, the central
canonical-model presentation yields the actual surface-group isomorphism. -/
def ClosedRiemannSurface.fundamentalGroupSurfaceGroupMulEquiv
    (R : ClosedRiemannSurface X) {g : ℕ} (hgenus : R.HasGenus g)
    (hPresentation : Unproved.HandleGroupPresentation g) (x : X) :
    FundamentalGroup X x ≃* LiZhongQC.surfaceGroup g := by
  let := R.toRiemannSurface.pathConnectedSpace
  let e := Classical.choice hgenus
  exact (fundamentalGroupCanonicalHandleMulEquiv e x).trans
    (Classical.choice hPresentation)

/-- Native handle-model genus implies the imported fundamental-group genus
under exactly the outstanding canonical presentation. Connectedness and the
complex atlas already prove path connectedness; no new connectedness
hypothesis or separate basepoint assumption is needed. -/
theorem ClosedRiemannSurface.sourceHasGenus
    (R : ClosedRiemannSurface X) {g : ℕ} (hgenus : R.HasGenus g)
    (hPresentation : Unproved.HandleGroupPresentation g) :
    LiZhongQC.HasGenus X g := by
  exact ⟨R.compactSpace, fun x =>
    ⟨R.fundamentalGroupSurfaceGroupMulEquiv hgenus hPresentation x⟩⟩

/-- The concrete canonical-model presentation also supplies the analytic-to-handle
comparison, through the actual real period map theorem. -/
theorem ClosedRiemannSurface.genusComparison_of_handleGroupPresentation
    (R : ClosedRiemannSurface X) {g : ℕ}
    (hPresentation : Unproved.HandleGroupPresentation g) :
    Unproved.Surfaces.GenusComparison R g := by
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  dsimp only [Unproved.Surfaces.GenusComparison]
  intro hgenus
  exact LiZhongQC.k22rr_genus_eq (R.sourceHasGenus hgenus hPresentation)

end LowDimensionalTopology.Geometry.Surfaces
