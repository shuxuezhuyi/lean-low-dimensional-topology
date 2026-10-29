module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarking
public import LowDimensionalTopology.Geometry.Teichmuller.DECoverDescent
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.SourceGenus
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannManifoldEquivalences

/-!
# Smooth representatives and surjectivity onto the QC quotient

Actual Douady--Earle descent gives a positive smooth representative of every
higher-genus quasiconformal marking in its free homotopy class. The comparison
preserves the actual carrier, topology and complex atlas. The separately
tracked canonical handle fundamental-group presentation supplies the genus
comparison; no surjectivity or smoothing conclusion is assumed.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v

/-- The all-chart/native analytic predicate and source biholomorphic predicate
also agree for arbitrary existing manifold structures. The named charted-space
instances allow the two carriers to coincide while their preferred chart
choices differ. -/
theorem analyticHomeomorph_ofManifold_iff_sourceBiholomorphic
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CX : ChartedSpace ℂ X] [CY : ChartedSpace ℂ Y]
    [MX : IsManifold 𝓘(ℂ) ω X] [MY : IsManifold 𝓘(ℂ) ω Y]
    (h : X ≃ₜ Y) :
    RiemannAnalyticMap (RiemannAtlas.ofManifold X) (RiemannAtlas.ofManifold Y) h ↔
      LiZhongQC.IsBiholomorphic (h : X → Y) := by
  constructor
  · intro hh
    exact ⟨hh.contMDiff_ofManifold.mdifferentiable (by simp), h.symm,
      (riemannAnalyticMap_homeomorph_symm h hh).contMDiff_ofManifold.mdifferentiable
        (by simp), h.symm_apply_apply, h.apply_symm_apply⟩
  · intro hh
    exact riemannAnalyticMap_of_contMDiff_ofManifold
      (LiZhongQC.k22u_mdifferentiable_contMDiff hh.1)

end LowDimensionalTopology.Geometry.Teichmuller

namespace LiZhongQC.ClosedRS

universe u

/-- Read the source closed surface in native notation on its unchanged carrier,
topology, and actual original complex chart set. -/
def toNative (S : LiZhongQC.ClosedRS.{u}) :
    LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface S.carrier :=
  LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface.ofManifold S.carrier

end LiZhongQC.ClosedRS

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u

namespace MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}


/-- Package a proved smooth positive representative of a source marking as an
actual native marked surface. -/
def ofSourceRepresentative :
    let := R.toRiemannAtlas.toChartedSpace
    (m : LiZhongQC.MarkedRS X) →
      (F : SmoothSurfaceEquiv R.toRiemannSurface m.X.toNative.toRiemannSurface) →
      PreservesComplexOrientation R.toRiemannAtlas m.X.toNative.toRiemannAtlas F.toHomeomorph →
      MarkedRiemannSurface.{u, u} R := by
  dsimp only
  let := R.toRiemannAtlas.toChartedSpace
  intro m F hF
  exact
    { carrier := m.X.carrier
      topology := m.X.topologicalSpace
      surface := m.X.toNative
      marking := F
      orientation_preserving := hF }

/-- The source marking and its proved native smooth representative are source
equivalent. The identity between the two target bundles is genuinely
biholomorphic even when their `chartAt` choices differ. -/
theorem source_equiv_ofSourceRepresentative :
    let := R.toRiemannAtlas.toChartedSpace
    ∀ (m : LiZhongQC.MarkedRS X)
      (F : SmoothSurfaceEquiv R.toRiemannSurface m.X.toNative.toRiemannSurface)
      (hF : PreservesComplexOrientation R.toRiemannAtlas m.X.toNative.toRiemannAtlas
        F.toHomeomorph),
      ContinuousMap.Homotopic (_root_.toContinuousMap F.toHomeomorph)
        (_root_.toContinuousMap m.marking) →
      LiZhongQC.MarkedRS.Equiv (ofSourceRepresentative (R := R) m F hF).toSource m := by
  dsimp only
  let := R.toRiemannAtlas.toChartedSpace
  intro m F hF hhom
  let N := ofSourceRepresentative (R := R) m F hF
  refine ⟨Homeomorph.refl m.X.carrier, ?_, hhom⟩
  apply (analyticHomeomorph_ofManifold_iff_sourceBiholomorphic
    (CX := N.toSource.X.chartedSpace) (CY := m.X.chartedSpace)
    (MX := N.toSource.X.isManifold) (MY := m.X.isManifold)
    (Homeomorph.refl m.X.carrier)).mp
  change RiemannAnalyticMap m.X.toNative.toRiemannAtlas m.X.toNative.toRiemannAtlas
    (id : m.X.carrier → m.X.carrier)
  exact RiemannAnalyticMap.id _

end MarkedRiemannSurface

namespace TeichmullerSpace

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- In higher genus, every actual QC-marked class has a native smooth positive
representative, proved by DE descent and its actual homotopy. -/
theorem toSource_surjective_of_sourceGenus {g : ℕ} (hg : 1 < g)
    (hX : LiZhongQC.HasGenus X g) : Function.Surjective (toSource R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  intro p
  refine Quot.inductionOn p ?_
  intro m
  have hY : LiZhongQC.HasGenus m.X.carrier g := by
    refine ⟨inferInstance, fun y => ?_⟩
    obtain ⟨e⟩ := hX.2 (m.marking.symm y)
    exact ⟨(fundamentalGroupHomeomorphMulEquiv m.marking.symm y).trans e⟩
  have hm : LiZhongQC.IsOrientationPreservingRS m.marking := by
    obtain ⟨K, _, hK⟩ := m.qc
    exact fun x => (hK x).isSensePreserving
  obtain ⟨F, hF, hhom⟩ := exists_smooth_in_homotopy_class_ofManifold hg hX hY m.marking hm
  let N : MarkedRiemannSurface.{u, u} R :=
    MarkedRiemannSurface.ofSourceRepresentative (R := R) m F hF
  refine ⟨mk N, ?_⟩
  change Quot.mk _ N.toSource = Quot.mk _ m
  exact Quot.sound (MarkedRiemannSurface.source_equiv_ofSourceRepresentative (R := R)
    m F hF hhom.symm)

/-- Native topological genus supplies the source genus under the single
explicit canonical handle fundamental-group presentation. -/
theorem toSource_surjective {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hPresentation : Unproved.HandleGroupPresentation g) :
    Function.Surjective (toSource R) :=
  toSource_surjective_of_sourceGenus R hg (R.sourceHasGenus hgenus hPresentation)

/-- The higher-genus QC quotient and native smooth-marked quotient agree,
conditional only on the separately tracked, concrete canonical handle
fundamental-group presentation. -/
def sourceEquiv {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hPresentation : Unproved.HandleGroupPresentation g) :
    TeichmullerSpace.{u, u} R ≃
      letI := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.TeichSpace X :=
  Equiv.ofBijective (toSource R)
    ⟨toSource_injective R, toSource_surjective R hg hgenus hPresentation⟩

end TeichmullerSpace

end LowDimensionalTopology.Geometry.Teichmuller
