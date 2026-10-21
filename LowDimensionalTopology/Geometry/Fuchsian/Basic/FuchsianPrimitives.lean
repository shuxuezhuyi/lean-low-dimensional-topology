/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianStabilizers
@[expose] public section
noncomputable section
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Generation is imposed at each actual fixed point in the compactified plane. -/
def GeneratesFixedStabilizers (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Prop :=
  ∀ z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, f.val z = z → Subgroup.zpowers f = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H z

/-- The primitive elliptic angle is the least positive rotation of a finite cyclic stabilizer.
Conjugacy permits interchanging the two fixed points, hence reversing the signed angle. -/
def HasLeastEllipticRotation (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Prop :=
  ∃ n : ℕ, 1 < n ∧ ∃ k : ℂˣ,
    IsConj f (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement k) ∧ (k : ℂ) = Complex.exp (2 *
      Real.pi * Complex.I / n)

/-- For an actual subgroup and actual transformation. -/
def IsPrimitive (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Prop :=
  f ∈ H ∧ GeneratesFixedStabilizers H f ∧
    (_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f ∨
      (_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f ∧ HasLeastEllipticRotation f))

theorem generatesFixedStabilizers_iff (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (f
  : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    GeneratesFixedStabilizers H f ↔
      ∀ z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, f.val z = z → ∀ g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,
        (g ∈ H ∧ g.val z = z) ↔ ∃ n : ℤ, f ^ n = g := by
  constructor
  · intro h z hz g
    rw [← _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer, ← h z hz,
      Subgroup.mem_zpowers_iff]
  · intro h z hz
    ext g
    rw [Subgroup.mem_zpowers_iff, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer]
    exact (h z hz g).symm

theorem IsPrimitive.mem {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (h : IsPrimitive H f) : f ∈ H := h.1

theorem IsPrimitive.generates {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (h : IsPrimitive H f) (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hz : f.val z = z) :
    Subgroup.zpowers f = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H z := h.2.1 z hz

theorem primitive_iff_of_parabolic {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) : IsPrimitive H f ↔ f ∈ H ∧ GeneratesFixedStabilizers H f := by
  exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,Or.inl hf⟩⟩

theorem primitive_iff_of_hyperbolic {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f) : IsPrimitive H f ↔ f ∈ H ∧ GeneratesFixedStabilizers H f := by
  exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,Or.inr (Or.inl hf)⟩⟩

theorem primitive_iff_of_elliptic {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) : IsPrimitive H f ↔
      f ∈ H ∧ GeneratesFixedStabilizers H f ∧ HasLeastEllipticRotation f := by
  constructor
  · intro h
    refine ⟨h.1,h.2.1,?_⟩
    rcases h.2.2 with hp | hh | he
    · exact False.elim (hf.not_parabolic hp)
    · exact False.elim (hh.1.not_elliptic hf)
    · exact he.2
  · rintro ⟨hm,hg,hr⟩
    exact ⟨hm,hg,Or.inr (Or.inr ⟨hf,hr⟩)⟩

theorem IsPrimitive.ne_one {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (h : IsPrimitive H f) : f ≠ 1 := by
  rcases h.2.2 with hp | hh | he
  · exact hp.1
  · exact hh.1.1
  · exact he.1.1

end LowDimensionalTopology.Geometry.Fuchsian
