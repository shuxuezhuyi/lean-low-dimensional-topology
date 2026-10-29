module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.SourceGenus
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The actual presentation of the one-handle surface

The two-generator, single-commutator presentation is explicitly isomorphic to
the product of two infinite cyclic groups. The genuine torus homeomorphism and
winding-number isomorphisms then identify this with the based fundamental group
of the canonical one-handle surface.
-/

@[expose] public section
noncomputable section

open scoped commutatorElement

namespace LowDimensionalTopology.Geometry.Surfaces

namespace SurfaceGroupOne

/-- The first generator in the specified one-handle presentation. -/
def a : LiZhongQC.surfaceGroup 1 := PresentedGroup.of (Sum.inl (0 : Fin 1))

/-- The second generator in the specified one-handle presentation. -/
def b : LiZhongQC.surfaceGroup 1 := PresentedGroup.of (Sum.inr (0 : Fin 1))

/-- The defining relation forces the two genuine presentation generators to commute. -/
theorem commute_generators : Commute a b := by
  let r : FreeGroup (Fin 1 ⊕ Fin 1) :=
    (List.ofFn fun i : Fin 1 =>
      FreeGroup.of (Sum.inl i : Fin 1 ⊕ Fin 1) * FreeGroup.of (Sum.inr i) *
        (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod
  change Commute
    (PresentedGroup.of (rels := {r}) (Sum.inl (0 : Fin 1)))
    (PresentedGroup.of (rels := {r}) (Sum.inr (0 : Fin 1)))
  apply commutatorElement_eq_one_iff_commute.mp
  rw [commutatorElement_def]
  have hrel : PresentedGroup.mk {r} r = 1 :=
    PresentedGroup.one_of_mem (Set.mem_singleton r)
  simpa only [r, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    mul_one, map_mul, map_inv, PresentedGroup.of] using hrel

/-- The two exponent vectors in the actual product of infinite cyclic groups. -/
def exponentVector : Fin 1 ⊕ Fin 1 → Multiplicative ℤ × Multiplicative ℤ :=
  Sum.elim (fun _ => (Multiplicative.ofAdd 1, 1))
    (fun _ => (1, Multiplicative.ofAdd 1))

/-- The presentation map recording both integer exponents. -/
def toIntPair : LiZhongQC.surfaceGroup 1 →* Multiplicative ℤ × Multiplicative ℤ :=
  PresentedGroup.toGroup (f := exponentVector) (by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst r
    simp [List.ofFn_succ, exponentVector])

@[simp]
theorem toIntPair_a : toIntPair a = (Multiplicative.ofAdd 1, 1) := by
  unfold toIntPair a
  exact PresentedGroup.toGroup.of _

@[simp]
theorem toIntPair_b : toIntPair b = (1, Multiplicative.ofAdd 1) := by
  unfold toIntPair b
  exact PresentedGroup.toGroup.of _

/-- The inverse sends a pair of integers to the corresponding product of powers. -/
def fromIntPair : Multiplicative ℤ × Multiplicative ℤ →* LiZhongQC.surfaceGroup 1 :=
  (zpowersHom _ a).noncommCoprod (zpowersHom _ b)
    (fun m n => commute_generators.zpow_zpow m.toAdd n.toAdd)

/-- The normal form map recovers both original presentation generators. -/
theorem fromIntPair_comp_toIntPair :
    fromIntPair.comp toIntPair = MonoidHom.id (LiZhongQC.surfaceGroup 1) := by
  apply PresentedGroup.ext
  intro i
  cases i with
  | inl j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change fromIntPair (toIntPair a) = a
      rw [toIntPair_a]
      change a ^ (1 : ℤ) * b ^ (0 : ℤ) = a
      simp only [zpow_one, zpow_zero, mul_one]
  | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change fromIntPair (toIntPair b) = b
      rw [toIntPair_b]
      change a ^ (0 : ℤ) * b ^ (1 : ℤ) = b
      simp only [zpow_zero, zpow_one, one_mul]

/-- Recording exponents recovers every integer pair, including negative powers. -/
theorem toIntPair_comp_fromIntPair :
    toIntPair.comp fromIntPair = MonoidHom.id (Multiplicative ℤ × Multiplicative ℤ) := by
  apply MonoidHom.ext
  rintro ⟨m, n⟩
  change toIntPair (a ^ m.toAdd * b ^ n.toAdd) = (m, n)
  rw [map_mul, map_zpow, map_zpow, toIntPair_a, toIntPair_b]
  apply Prod.ext
  · apply Multiplicative.ext
    simp
  · apply Multiplicative.ext
    simp

/-- The one-handle presentation is genuinely the product of two infinite cyclic groups. -/
def intPairMulEquiv : LiZhongQC.surfaceGroup 1 ≃*
    Multiplicative ℤ × Multiplicative ℤ :=
  MonoidHom.toMulEquiv toIntPair fromIntPair
    fromIntPair_comp_toIntPair toIntPair_comp_fromIntPair

end SurfaceGroupOne

/-- The actual canonical one-handle surface has the specified surface-group
presentation at its original chosen basepoint. The torus winding isomorphism is
applied at the image of that exact point, so no basepoint replacement is assumed. -/
theorem handleGroupPresentation_one : Unproved.HandleGroupPresentation 1 := by
  let e := canonicalHandleSurfaceOneHomeomorph
  let x := canonicalHandleBasePoint 1
  exact ⟨((fundamentalGroupHomeomorphMulEquiv e x).trans
    (torusProductFundamentalGroupEquiv (e x))).trans SurfaceGroupOne.intPairMulEquiv.symm⟩

/-- The analytic-to-topological genus comparison is unconditional in genus one. -/
theorem ClosedRiemannSurface.genusComparison_one {X : Type*} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) : Unproved.Surfaces.GenusComparison R 1 :=
  R.genusComparison_of_handleGroupPresentation handleGroupPresentation_one

end LowDimensionalTopology.Geometry.Surfaces
