/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalGeneratorMarkingComparison
public import LowDimensionalTopology.Geometry.Surfaces.Topology.OriginalCanonicalCutHomExt
public import LowDimensionalTopology.Geometry.Teichmuller.HalfPlaneCommonPathHomotopy
public import LowDimensionalTopology.Geometry.Teichmuller.Space
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.HalfPlaneUniformization

/-!
# The literal comparison of the two marked quotients

An original smooth marking sends the fixed reference point and ordered
classes to their actual images on its unchanged target. Geometric transport
provides canonicality of that family. Homotopy transport makes this literal
map well defined, while the actual canonical cut and half-plane homotopy
criterion give injectivity. Prescribed positive smooth realization gives
surjectivity onto the quotient of original geometrically marked surfaces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

variable {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
  (hTransport : Unproved.Teichmuller.OriginalCanonicalFamilyMarkingTransport hg B)

/-- Retain the actual target and send the fixed original point and every
ordered class through the given original smooth marking. -/
def originalGeneratorMarkedTarget (m : MarkedRiemannSurface.{0, 0} B.surface) :
    OriginalGeneratorMarkedSurface g where
  carrier := m.carrier
  topology := m.topology
  surface := m.surface
  genus := by
    obtain ⟨e⟩ := B.genus
    exact ⟨m.marking.toHomeomorph.symm.trans e⟩
  point := m.markingMap B.point
  classes := fun d => FundamentalGroup.map m.markingMap B.point (B.classes d)
  canonical := hTransport m

theorem originalGeneratorMarkedTarget_equivalent
    {m n : MarkedRiemannSurface.{0, 0} B.surface}
    (hmn : MarkedRiemannSurface.Equivalent m n) :
    (originalGeneratorMarkedTarget hg B hTransport m).Equivalent
      (originalGeneratorMarkedTarget hg B hTransport n) := by
  obtain ⟨k, hk, H⟩ := hmn
  obtain ⟨H⟩ := H
  apply OriginalGeneratorMarkedSurface.equivalent_symm
  dsimp only [OriginalGeneratorMarkedSurface.Equivalent, originalGeneratorMarkedTarget]
  refine ⟨k, hk, H.evalAt B.point, ?_⟩
  intro d
  simpa only [FundamentalGroup.map_comp, MonoidHom.comp_apply] using
    (homotopy_basedLoop_transport
      ((⟨k, k.continuous⟩ : C(m.carrier, n.carrier)).comp m.markingMap)
      n.markingMap H B.point (B.classes d))

/-- The original target and actual induced ordered family define a map from
the fixed-reference smooth-marked quotient to the geometrically marked
quotient. Its only constructor premise is geometric canonicality transport. -/
def originalGeneratorComparison :
    TeichmullerSpace.{0, 0} B.surface → OriginalGeneratorTeichmullerSpace g :=
  Quotient.lift
    (fun m => OriginalGeneratorTeichmullerSpace.mk
      (originalGeneratorMarkedTarget hg B hTransport m))
    (by
      intro m n hmn
      exact Quotient.sound (originalGeneratorMarkedTarget_equivalent hg B hTransport hmn))

/-- On a genuine representative the comparison is exactly the unchanged
target with the actual image point and all induced ordered classes. -/
theorem originalGeneratorComparison_mk (m : MarkedRiemannSurface.{0, 0} B.surface) :
    originalGeneratorComparison hg B hTransport (TeichmullerSpace.mk m) =
      OriginalGeneratorTeichmullerSpace.mk (originalGeneratorMarkedTarget hg B hTransport m) := rfl

/-- The same literal comparison is bijective under geometric family
transport and prescribed positive smooth realization. The injection uses
the actual common-path condition, and the surjection retains the prescribed
target, map and one transporting path. -/
theorem originalGeneratorComparison_bijective
    (hRealize : Unproved.Teichmuller.OriginalGeneratorPrescribedPositiveSmoothRealization hg B) :
    Function.Bijective (originalGeneratorComparison hg B hTransport) := by
  classical
  have hpos : 0 < g := lt_trans Nat.zero_lt_one hg
  obtain ⟨D, hD⟩ : HasOriginalCanonicalCut B.surface g hpos B.point B.classes := by
    cases g with
    | zero => omega
    | succ n => exact B.canonical
  let := B.surface.t2Space
  let := B.surface.connectedSpace
  let := B.surface.toRiemannAtlas.toChartedSpace
  obtain ⟨M₀⟩ := (isHyperbolicType_iff_nonempty_model B.surface.toRiemannSurface).mp
    (B.surface.isHyperbolicType_of_genus_ge_two (by omega) B.genus)
  obtain ⟨Γ₀, _, hp₀⟩ := M₀.exists_halfPlaneCover_uniformization
  constructor
  · intro p q
    refine Quotient.inductionOn₂ p q ?_
    intro m n heq
    apply Quotient.sound
    change OriginalGeneratorTeichmullerSpace.mk (originalGeneratorMarkedTarget hg B hTransport m) =
      OriginalGeneratorTeichmullerSpace.mk (originalGeneratorMarkedTarget hg B hTransport n) at heq
    have hEquivalent : (originalGeneratorMarkedTarget hg B hTransport m).Equivalent
        (originalGeneratorMarkedTarget hg B hTransport n) := Quotient.exact heq
    dsimp only [OriginalGeneratorMarkedSurface.Equivalent, originalGeneratorMarkedTarget] at hEquivalent
    obtain ⟨h, hh, c, hc⟩ := hEquivalent
    let f : B.carrier ≃ₜ m.carrier := n.marking.toHomeomorph.trans h
    let k : B.carrier ≃ₜ m.carrier := m.marking.toHomeomorph
    have hslots : ∀ d : Fin g × Fin 2,
        FundamentalGroup.fundamentalGroupMulEquivOfPath c
          (FundamentalGroup.map (f : C(B.carrier, m.carrier)) B.point (D.family d)) =
            FundamentalGroup.map (k : C(B.carrier, m.carrier)) B.point (D.family d) := by
      intro d
      rw [congrFun hD d]
      change FundamentalGroup.fundamentalGroupMulEquivOfPath c
        (FundamentalGroup.map ((_root_.toContinuousMap h).comp n.markingMap) B.point
          (B.classes d)) = FundamentalGroup.map m.markingMap B.point (B.classes d)
      rw [FundamentalGroup.map_comp, MonoidHom.comp_apply]
      exact hc d
    have hall := D.transport_all (f : C(B.carrier, m.carrier))
      (k : C(B.carrier, m.carrier)) c hslots
    let := m.surface.t2Space
    let := m.surface.connectedSpace
    let := m.surface.toRiemannAtlas.toChartedSpace
    have hmgenus : m.surface.HasGenus g :=
      (originalGeneratorMarkedTarget hg B hTransport m).genus
    obtain ⟨M₁⟩ := (isHyperbolicType_iff_nonempty_model m.surface.toRiemannSurface).mp
      (m.surface.isHyperbolicType_of_genus_ge_two (by omega) hmgenus)
    obtain ⟨Γ₁, _, hp₁⟩ := M₁.exists_halfPlaneCover_uniformization
    have H := homotopic_of_halfPlane_commonPath hp₀ hp₁ f k B.point c hall
    change ContinuousMap.Homotopic ((_root_.toContinuousMap h).comp n.markingMap)
      m.markingMap at H
    exact MarkedRiemannSurface.equivalent_symm ⟨h, hh, H⟩
  · intro q
    refine Quotient.inductionOn q ?_
    intro N
    obtain ⟨F, hF, c, hc⟩ := hRealize N
    let m : MarkedRiemannSurface.{0, 0} B.surface :=
      { carrier := N.carrier
        topology := N.topology
        surface := N.surface
        marking := F
        orientation_preserving := hF }
    refine ⟨TeichmullerSpace.mk m, ?_⟩
    change OriginalGeneratorTeichmullerSpace.mk (originalGeneratorMarkedTarget hg B hTransport m) =
      OriginalGeneratorTeichmullerSpace.mk N
    apply Quotient.sound
    apply OriginalGeneratorMarkedSurface.equivalent_symm
    refine ⟨Homeomorph.refl N.carrier, RiemannAnalyticMap.id _, c, ?_⟩
    intro d
    change FundamentalGroup.fundamentalGroupMulEquivOfPath c
      (FundamentalGroup.map (ContinuousMap.id N.carrier) (F.toHomeomorph B.point)
        (FundamentalGroup.map
          (⟨F.toHomeomorph, F.toHomeomorph.continuous⟩ : C(B.carrier, N.carrier))
          B.point (B.classes d))) = N.classes d
    rw [FundamentalGroup.map_id]
    change FundamentalGroup.fundamentalGroupMulEquivOfPath c
      (FundamentalGroup.map
        (⟨F.toHomeomorph, F.toHomeomorph.continuous⟩ : C(B.carrier, N.carrier))
        B.point (B.classes d)) = N.classes d
    exact hc d

end LowDimensionalTopology.Geometry.Teichmuller
