module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalCanonicalCutQCPositiveTransport
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalGeneratorMarkingComparison
public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarking

/-!
# The same original cut under an actual quasiconformal marking

The supplied positive-field obligation gives the literal composed cut. Its
vertex and every ordered side class are transported through the same map.
Compact positive smooth markings are already quasiconformal, so the same
geometric premise also gives their canonical-family transport statement.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

open HandlePresentation

namespace OriginalOrientedCanonicalCut

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {R : ClosedRiemannSurface X} {g : ℕ} {hg : 1 < g} {p : X}
  (D : OriginalOrientedCanonicalCut R g (lt_trans Nat.zero_lt_one hg) p)

/-- The actual quasiconformal map transports the same cut and its vertex. -/
def mapQC
    (hGeom : Unproved.Teichmuller.OriginalCanonicalCutQCPositiveTransport R hg p D)
    (S : ClosedRiemannSurface Y) (f : X ≃ₜ Y)
    (hf : letI := R.toRiemannAtlas.toChartedSpace
      letI := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsQCRS f) :
    OriginalOrientedCanonicalCut S g (lt_trans Nat.zero_lt_one hg) (f p) where
  polygon := f.symm.trans D.polygon
  vertex := by
    change D.polygon (f.symm (f p)) = (boundaryBase g).val
    rw [f.symm_apply_apply]
    exact D.vertex
  positive := hGeom S f hf

/-- Each actual side path is the image of the same original side path. -/
theorem mapQC_loop
    (hGeom : Unproved.Teichmuller.OriginalCanonicalCutQCPositiveTransport R hg p D)
    (S : ClosedRiemannSurface Y) (f : X ≃ₜ Y)
    (hf : letI := R.toRiemannAtlas.toChartedSpace
      letI := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsQCRS f) (i : Fin g × Fin 2) :
    (D.mapQC (hg := hg) hGeom S f hf).loop
      (hg := lt_trans Nat.zero_lt_one hg) i = (D.loop i).map f.continuous := by
  apply Path.ext
  funext t
  rfl

/-- Every ordered based class is the actual induced image at the image point. -/
theorem mapQC_family
    (hGeom : Unproved.Teichmuller.OriginalCanonicalCutQCPositiveTransport R hg p D)
    (S : ClosedRiemannSurface Y) (f : X ≃ₜ Y)
    (hf : letI := R.toRiemannAtlas.toChartedSpace
      letI := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsQCRS f) (i : Fin g × Fin 2) :
    (D.mapQC (hg := hg) hGeom S f hf).family
      (hg := lt_trans Nat.zero_lt_one hg) i =
      FundamentalGroup.map (⟨f, f.continuous⟩ : C(X, Y)) p (D.family i) := by
  change pathClass ((D.mapQC (hg := hg) hGeom S f hf).loop
      (hg := lt_trans Nat.zero_lt_one hg) i) =
    FundamentalGroup.map (⟨f, f.continuous⟩ : C(X, Y)) p (pathClass (D.loop i))
  rw [D.mapQC_loop (hg := hg) hGeom S f hf]
  exact (TauCeti.FundamentalGroup.map_fromPath
    (⟨f, f.continuous⟩ : C(X, Y)) p (D.loop i)).symm

end OriginalOrientedCanonicalCut

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

/-- An actual quasiconformal marking transports every prescribed ordered
class through the same positive cut at its actual image basepoint. -/
theorem originalCanonicalFamily_of_qcCutPositiveTransport
    {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
    (D : OriginalOrientedCanonicalCut B.surface g
      (lt_trans Nat.zero_lt_one hg) B.point)
    (hD : D.family = B.classes)
    (hGeom : Unproved.Teichmuller.OriginalCanonicalCutQCPositiveTransport
      B.surface hg B.point D)
    {Y : Type} [TopologicalSpace Y] (S : ClosedRiemannSurface Y)
    (f : B.carrier ≃ₜ Y)
    (hf : letI := B.surface.toRiemannAtlas.toChartedSpace
      letI := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsQCRS f) :
    IsOriginalCanonicalFamily S g (f B.point)
      (fun i : Fin g × Fin 2 =>
        FundamentalGroup.map (⟨f, f.continuous⟩ : C(B.carrier, Y))
          B.point (B.classes i)) := by
  cases g with
  | zero => omega
  | succ n =>
      change HasOriginalCanonicalCut S (n + 1) (Nat.zero_lt_succ n) (f B.point) _
      refine ⟨D.mapQC (hg := hg) hGeom S f hf, ?_⟩
      funext i
      rw [D.mapQC_family (hg := hg) hGeom S f hf, hD]

/-- The existing smooth canonical-family transport follows from the same
geometric premise, using the proved compact positive-smooth QC bound. -/
theorem originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport
    {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
    (D : OriginalOrientedCanonicalCut B.surface g
      (lt_trans Nat.zero_lt_one hg) B.point)
    (hD : D.family = B.classes)
    (hGeom : Unproved.Teichmuller.OriginalCanonicalCutQCPositiveTransport
      B.surface hg B.point D) :
    Unproved.Teichmuller.OriginalCanonicalFamilyMarkingTransport hg B := by
  intro m
  let := B.surface.compactSpace
  have hqc :
      letI := B.surface.toRiemannAtlas.toChartedSpace
      letI := m.surface.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsQCRS m.marking.toHomeomorph :=
    m.marking.isQCRS_of_compact m.orientation_preserving
  exact originalCanonicalFamily_of_qcCutPositiveTransport hg B D hD hGeom
    m.surface m.marking.toHomeomorph hqc

end LowDimensionalTopology.Geometry.Teichmuller
