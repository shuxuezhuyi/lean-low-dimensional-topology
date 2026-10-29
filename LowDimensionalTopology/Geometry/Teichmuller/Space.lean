module

public import LowDimensionalTopology.Geometry.Teichmuller.Marking
public import Mathlib.Topology.Homotopy.Basic

/-!
# Teichmüller equivalence of marked closed surfaces

Two marked surfaces are equivalent when a biholomorphic homeomorphism between
their targets carries one marking into the free homotopy class of the other.
The quotient here is the set of marked complex structures; no topology or
comparison with a fixed-carrier quotient is asserted in this file.
-/

@[expose] public section

noncomputable section

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v

namespace MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- A biholomorphic change of target compatible with the marking up to free homotopy. -/
def Equivalent (M N : MarkedRiemannSurface.{u, v} R) : Prop :=
  ∃ h : M.carrier ≃ₜ N.carrier,
    RiemannAnalyticMap M.surface.toRiemannAtlas N.surface.toRiemannAtlas h ∧
      ContinuousMap.Homotopic ((_root_.toContinuousMap h).comp M.markingMap) N.markingMap

/-- The identity target isomorphism witnesses equivalence to itself. -/
theorem equivalent_refl (M : MarkedRiemannSurface.{u, v} R) : Equivalent M M := by
  refine ⟨Homeomorph.refl _, RiemannAnalyticMap.id _, ?_⟩
  exact ContinuousMap.Homotopic.refl M.markingMap

/-- Inverting the target isomorphism reverses Teichmüller equivalence. -/
theorem equivalent_symm {M N : MarkedRiemannSurface.{u, v} R}
    (hMN : Equivalent M N) : Equivalent N M := by
  obtain ⟨h, hanalytic, hmark⟩ := hMN
  refine ⟨h.symm, riemannAnalyticMap_homeomorph_symm h hanalytic, ?_⟩
  have hc := (ContinuousMap.Homotopic.refl (_root_.toContinuousMap h.symm)).comp hmark
  have hcancel : (_root_.toContinuousMap h.symm).comp ((_root_.toContinuousMap h).comp M.markingMap) =
      M.markingMap := by
    ext x
    exact h.symm_apply_apply _
  rw [hcancel] at hc
  exact hc.symm

/-- Composition of biholomorphic target maps and homotopies is transitive. -/
theorem equivalent_trans {M N P : MarkedRiemannSurface.{u, v} R}
    (hMN : Equivalent M N) (hNP : Equivalent N P) : Equivalent M P := by
  obtain ⟨h, hh, hmark⟩ := hMN
  obtain ⟨k, hk, kmark⟩ := hNP
  refine ⟨h.trans k, hk.comp hh, ?_⟩
  have hc := (ContinuousMap.Homotopic.refl (_root_.toContinuousMap k)).comp hmark
  exact hc.trans kmark

/-- The actual marked-surface equivalence relation. -/
def setoid (R : ClosedRiemannSurface X) : Setoid (MarkedRiemannSurface.{u, v} R) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

end MarkedRiemannSurface

/-- Marked closed complex structures on a fixed closed reference surface,
modulo biholomorphic target changes compatible with the markings up to homotopy. -/
def TeichmullerSpace {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) :=
  Quotient (MarkedRiemannSurface.setoid.{u, v} R)

namespace TeichmullerSpace

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The point represented by a marked surface. -/
def mk (M : MarkedRiemannSurface.{u, v} R) : TeichmullerSpace.{u, v} R :=
  Quotient.mk (MarkedRiemannSurface.setoid R) M

/-- Equality in the quotient is exactly the original equivalence relation. -/
theorem mk_eq_mk_iff (M N : MarkedRiemannSurface.{u, v} R) :
    mk M = mk N ↔ MarkedRiemannSurface.Equivalent M N := by
  constructor
  · exact Quotient.exact
  · intro h
    exact @Quotient.sound _ (MarkedRiemannSurface.setoid R) M N h

/-- The reference complex structure with its identity marking. -/
def basePoint (R : ClosedRiemannSurface X) : TeichmullerSpace.{u, u} R :=
  mk (MarkedRiemannSurface.refl R)

instance (R : ClosedRiemannSurface X) : Nonempty (TeichmullerSpace.{u, u} R) :=
  ⟨basePoint R⟩

end TeichmullerSpace

end LowDimensionalTopology.Geometry.Teichmuller
