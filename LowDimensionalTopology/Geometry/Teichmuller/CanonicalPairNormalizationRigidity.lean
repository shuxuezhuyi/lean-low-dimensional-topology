module

public import LowDimensionalTopology.Geometry.Mobius.Classification.MobiusTypes
public import Mathlib.Data.Fintype.EquivFin

/-!
# Rigidity of the dynamically normalized distinguished canonical pair

The source's attracting and repelling labels force a conjugator to fix the
three actual boundary points zero, one and infinity. Mere fixed-point
membership does not supply this conclusion. This proof component does not
construct a canonical marking or its normalized Fuchsian model.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Filter Topology
open scoped OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller

open Mobius

private theorem attractingRepellingPair_unique
    {f : complexMobiusGroup} {a b c d : ExtendedComplex}
    (h : IsMobiusAttractingRepellingPair f a b)
    (k : IsMobiusAttractingRepellingPair f c d) : a = c ∧ b = d := by
  classical
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset ({a, b, c, d} : Finset ExtendedComplex)
  have hz' : z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ z ≠ d := by simpa using hz
  exact ⟨tendsto_nhds_unique (h.2.2.2.1 z hz'.2.1) (k.2.2.2.1 z hz'.2.2.2),
    tendsto_nhds_unique (h.2.2.2.2 z hz'.1) (k.2.2.2.2 z hz'.2.2.1)⟩

/-- A conjugacy between two distinguished canonical pairs satisfying the
book's dynamically labelled normalization is the identity projective map. -/
theorem normalizedCanonicalPair_conjugator_eq_one
    (A B A' B' q : complexMobiusGroup)
    (hA : MobiusAttractiveFixedPoint A (1 : ℂ))
    (hA' : MobiusAttractiveFixedPoint A' (1 : ℂ))
    (hB : IsMobiusAttractingRepellingPair B ∞ (0 : ℂ))
    (hB' : IsMobiusAttractingRepellingPair B' ∞ (0 : ℂ))
    (hconjA : A' = q * A * q⁻¹) (hconjB : B' = q * B * q⁻¹) : q = 1 := by
  have hBq : IsMobiusAttractingRepellingPair B' (q.val ∞) (q.val (0 : ℂ)) := by
    rw [hconjB]
    exact hB.conjugation q
  have hends := attractingRepellingPair_unique hBq hB'
  obtain ⟨r, hr⟩ := hA
  obtain ⟨r', hr'⟩ := hA'
  have hAq : IsMobiusAttractingRepellingPair A' (q.val (1 : ℂ)) (q.val r) := by
    rw [hconjA]
    exact hr.conjugation q
  have hone := (attractingRepellingPair_unique hAq hr').1
  exact mobius_eq_one_of_fixes_zero_one_infty q hends.2 hone hends.1

end LowDimensionalTopology.Geometry.Teichmuller
