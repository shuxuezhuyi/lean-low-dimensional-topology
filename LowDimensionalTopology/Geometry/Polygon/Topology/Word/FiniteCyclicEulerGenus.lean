/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Topology.Word.FiniteCyclicEulerNormalization
public import LowDimensionalTopology.Geometry.Surfaces.Topology.ClassificationBridge
public import LowDimensionalTopology.External.LeanPool.ClassificationOfSurfaces.NormalForm
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation
namespace LowDimensionalTopology.Geometry.Surfaces.CyclicSurface

theorem normalizationResult_closed_genus {P : ValidPresentation}
    (r : NormalizationResult P) (hc : IsClosed P.presentation)
    (ho : IsCoherentlyOrientable P.presentation) :
    ∃g,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus (P.presentation.PolygonalRealization
      P.valid) g ∧
      eulerCharacteristic P.presentation=2-2*(g : ℤ) := by
  rcases r with ⟨N,hN,hPN⟩
  rcases closed_coherent_normalizationResult_euler (show NormalizationResult P from ⟨N,hN,hPN⟩) hc ho with h|h
  · change N=NormalForm.sphere ∧ eulerCharacteristic P.presentation=2 at h
    obtain ⟨rfl,hχ⟩ := h
    have e : P.presentation.PolygonalRealization P.valid≃ₜSphereRepresentative :=
      (show NormalizationResult P from ⟨NormalForm.sphere,hN,hPN⟩).realizationHomeomorph.trans
        NormalForm.canonicalSphereRealizationHomeomorph
    refine ⟨0,_root_.LowDimensionalTopology.Geometry.Surfaces.hasTopologicalGenus_zero_iff.mpr ⟨e⟩,?_⟩
    simpa only [Nat.cast_zero,mul_zero,sub_zero] using hχ
  · change ∃g,0<g ∧ N=NormalForm.orientable g 0 ∧
      eulerCharacteristic P.presentation=2-2*(g : ℤ) at h
    obtain ⟨g,hg,rfl,hχ⟩ := h
    have e : P.presentation.PolygonalRealization P.valid≃ₜQuot (OrientableRel g 0) :=
      (show NormalizationResult P from ⟨NormalForm.orientable g 0,hN,hPN⟩).realizationHomeomorph.trans
        (NormalForm.canonicalOrientableRealizationHomeomorph (Or.inl hg))
    exact ⟨g,_root_.LowDimensionalTopology.Geometry.Surfaces.hasTopologicalGenus_of_leanPool_closed_orientable hg e,hχ⟩

theorem closed_coherent_connected_genus (P : ValidPresentation)
    (hconn : P.presentation.IsConnected) (hc : IsClosed P.presentation)
    (ho : IsCoherentlyOrientable P.presentation) :
    ∃g,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus (P.presentation.PolygonalRealization
      P.valid) g ∧
      eulerCharacteristic P.presentation=2-2*(g : ℤ) :=
  normalizationResult_closed_genus (normalizeConnectedToCanonical P hconn) hc ho

theorem genus_euler_of_finite_cyclic_realization {X : Type*} [TopologicalSpace X]
    (P : ValidPresentation) (hconn : P.presentation.IsConnected)
    (hc : IsClosed P.presentation) (ho : IsCoherentlyOrientable P.presentation)
    (e : X≃ₜP.presentation.PolygonalRealization P.valid) :
    ∃g,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus X g ∧ eulerCharacteristic P.presentation=2-2*(g : ℤ) := by
  obtain ⟨g,⟨eg⟩,hχ⟩ := closed_coherent_connected_genus P hconn hc ho
  exact ⟨g,⟨e.trans eg⟩,hχ⟩

end LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
