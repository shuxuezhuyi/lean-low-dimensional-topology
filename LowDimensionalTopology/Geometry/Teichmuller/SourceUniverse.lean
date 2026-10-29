module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarking
public import LowDimensionalTopology.Geometry.Teichmuller.ConformalSmooth
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Covering
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Matching the source marking universe

The imported QC library puts reference and target carriers in the same universe.
The native definition permits different universes. Lifting both actual carriers
to their maximum universe resolves this discrepancy through actual analytic
homeomorphisms, without identifying distinct universes or changing the meaning
of a marking.
-/

@[expose] public section

noncomputable section

namespace LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface

universe u v

/-- Transport a closed complex surface along an actual homeomorphism, using the
existing atlas pullback along a local homeomorphism. -/
def pullbackHomeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface Y) (e : X ≃ₜ Y) : ClosedRiemannSurface X where
  toRiemannSurface :=
    { toRiemannAtlas := R.toRiemannAtlas.liftLocalHomeomorph e e.isLocalHomeomorph
      t2Space := by
        let := R.t2Space
        exact e.isEmbedding.t2Space
      connectedSpace := by
        let := R.toRiemannSurface.pathConnectedSpace
        let := e.symm.pathConnectedSpace
        infer_instance }
  compactSpace := by
    let := R.compactSpace
    exact e.symm.compactSpace

/-- The transporting homeomorphism is genuinely analytic in the pulled-back
atlas and the original atlas. -/
theorem pullbackHomeomorph_analytic {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface Y) (e : X ≃ₜ Y) :
    RiemannAnalyticMap (R.pullbackHomeomorph e).toRiemannAtlas R.toRiemannAtlas e :=
  R.toRiemannAtlas.liftLocalHomeomorph_projection_analytic e e.isLocalHomeomorph

/-- The actual complex surface on the universe lift of its carrier. -/
def ulift {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) :
    ClosedRiemannSurface (ULift.{v, u} X) :=
  R.pullbackHomeomorph Homeomorph.ulift

/-- The lift projection is an analytic homeomorphism, rather than a mere
equivalence of underlying point sets. -/
theorem ulift_analytic {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) :
    RiemannAnalyticMap
      (R.ulift : ClosedRiemannSurface (ULift.{v, u} X)).toRiemannAtlas
      R.toRiemannAtlas (Homeomorph.ulift : ULift.{v, u} X ≃ₜ X) :=
  R.pullbackHomeomorph_analytic Homeomorph.ulift

end LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v

namespace MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- Lift reference and target to a common universe, transporting the marking
through the actual analytic lift projections and their real smooth inverses. -/
def liftUniverses (M : MarkedRiemannSurface.{u, v} R) :
    MarkedRiemannSurface.{max u v, max u v}
      (R.ulift : ClosedRiemannSurface (ULift.{v, u} X)) := by
  let R' : ClosedRiemannSurface (ULift.{v, u} X) := R.ulift
  let S' : ClosedRiemannSurface (ULift.{u, v} M.carrier) := M.surface.ulift
  let a : SmoothSurfaceEquiv R'.toRiemannSurface R.toRiemannSurface :=
    .ofConformalHomeomorph R'.toRiemannSurface R.toRiemannSurface
      Homeomorph.ulift R.ulift_analytic
  let b : SmoothSurfaceEquiv S'.toRiemannSurface M.surface.toRiemannSurface :=
    .ofConformalHomeomorph S'.toRiemannSurface M.surface.toRiemannSurface
      Homeomorph.ulift M.surface.ulift_analytic
  have ha : PreservesComplexOrientation R'.toRiemannAtlas R.toRiemannAtlas
      a.toHomeomorph :=
    SmoothSurfaceEquiv.ofConformalHomeomorph_preservesComplexOrientation
      R'.toRiemannSurface R.toRiemannSurface Homeomorph.ulift R.ulift_analytic
  have hb : PreservesComplexOrientation S'.toRiemannAtlas M.surface.toRiemannAtlas
      b.toHomeomorph :=
    SmoothSurfaceEquiv.ofConformalHomeomorph_preservesComplexOrientation
      S'.toRiemannSurface M.surface.toRiemannSurface
      Homeomorph.ulift M.surface.ulift_analytic
  refine
    { carrier := ULift.{u, v} M.carrier
      topology := inferInstance
      surface := S'
      marking := (a.trans M.marking).trans b.symm
      orientation_preserving := ?_ }
  have hfirst := M.orientation_preserving.comp ha a.toHomeomorph.continuous
  have hlast := (PreservesComplexOrientation.homeomorph_symm b.toHomeomorph hb).comp
    hfirst (M.marking.toHomeomorph.continuous.comp a.toHomeomorph.continuous)
  exact hlast

@[simp]
theorem liftUniverses_marking_apply (M : MarkedRiemannSurface.{u, v} R)
    (x : ULift.{v, u} X) :
    M.liftUniverses.marking.toHomeomorph x =
      ULift.up (M.marking.toHomeomorph x.down) := rfl

/-- Changing universes preserves the original marked equivalence relation. -/
theorem Equivalent.liftUniverses {M N : MarkedRiemannSurface.{u, v} R}
    (hMN : Equivalent M N) : Equivalent M.liftUniverses N.liftUniverses := by
  obtain ⟨h, hh, hhom⟩ := hMN
  let h' : ULift.{u, v} M.carrier ≃ₜ ULift.{u, v} N.carrier :=
    Homeomorph.ulift.trans (h.trans Homeomorph.ulift.symm)
  refine ⟨h', ?_, ?_⟩
  · exact RiemannAnalyticMap.liftLocalHomeomorph
      (Homeomorph.ulift : ULift.{u, v} M.carrier ≃ₜ M.carrier)
      (Homeomorph.ulift : ULift.{u, v} N.carrier ≃ₜ N.carrier)
      Homeomorph.ulift.isLocalHomeomorph Homeomorph.ulift.isLocalHomeomorph
      h h' hh h'.continuous (fun _ => rfl)
  · have hpre := hhom.comp (ContinuousMap.Homotopic.refl
      (_root_.toContinuousMap (Homeomorph.ulift : ULift.{v, u} X ≃ₜ X)))
    exact (ContinuousMap.Homotopic.refl
      (_root_.toContinuousMap
        (Homeomorph.ulift.symm : N.carrier ≃ₜ ULift.{u, v} N.carrier))).comp hpre

/-- Lift projection homeomorphisms also reflect marked equivalence. Their
analytic inverses and the inverse lift on the reference transport each witness
back to the original carriers. -/
theorem equivalent_of_liftUniverses {M N : MarkedRiemannSurface.{u, v} R}
    (hMN : Equivalent M.liftUniverses N.liftUniverses) : Equivalent M N := by
  obtain ⟨h, hh, hhom⟩ := hMN
  let pM : ULift.{u, v} M.carrier ≃ₜ M.carrier := Homeomorph.ulift
  let pN : ULift.{u, v} N.carrier ≃ₜ N.carrier := Homeomorph.ulift
  let h' : M.carrier ≃ₜ N.carrier := pM.symm.trans (h.trans pN)
  refine ⟨h', ?_, ?_⟩
  · exact N.surface.ulift_analytic.comp
      (hh.comp (riemannAnalyticMap_homeomorph_symm pM M.surface.ulift_analytic))
  · have hpre := hhom.comp (ContinuousMap.Homotopic.refl
      (_root_.toContinuousMap (Homeomorph.ulift.symm : X ≃ₜ ULift.{v, u} X)))
    exact (ContinuousMap.Homotopic.refl (_root_.toContinuousMap pN)).comp hpre

end MarkedRiemannSurface

namespace TeichmullerSpace

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The faithful change of universe on actual smooth-marked Teichmüller classes. -/
def liftUniverses :
    TeichmullerSpace.{u, v} R →
      TeichmullerSpace.{max u v, max u v}
        (R.ulift : ClosedRiemannSurface (ULift.{v, u} X)) :=
  Quotient.map' MarkedRiemannSurface.liftUniverses
    (fun _ _ h => h.liftUniverses)

theorem liftUniverses_injective : Function.Injective (liftUniverses.{u, v} R) := by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro M N h
  exact Quotient.sound
    (MarkedRiemannSurface.equivalent_of_liftUniverses (Quotient.exact h))

/-- For independently sized native reference and target carriers, lift both to
the maximum universe before using the imported QC quotient. -/
def toSourceLifted :
    TeichmullerSpace.{u, v} R →
      letI := (R.ulift : ClosedRiemannSurface (ULift.{v, u} X)).toRiemannAtlas.toChartedSpace
      LiZhongQC.TeichSpace (ULift.{v, u} X) :=
  (toSource (R.ulift : ClosedRiemannSurface (ULift.{v, u} X))) ∘ liftUniverses R

theorem toSourceLifted_injective : Function.Injective (toSourceLifted.{u, v} R) :=
  (toSource_injective (R.ulift : ClosedRiemannSurface (ULift.{v, u} X))).comp
    (liftUniverses_injective R)

end TeichmullerSpace

end LowDimensionalTopology.Geometry.Teichmuller
