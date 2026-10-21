/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Group actions before the Möbius classification

Permutations, fixed points, stabilizers and orbits; the orbit-coset bijection;
conjugacy of subgroups; and the effect of conjugation and commutation on fixed
points. The statements apply to arbitrary group actions.
-/

@[expose] public section

open scoped Pointwise

universe u v

namespace LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions

/-- A permutation is a bijection of a set with itself. -/
abbrev Permutation (X : Type v) := Equiv.Perm X

variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

/-- The permutation induced by an element of the acting group. -/
def actionPermutation (g : G) : Permutation X := MulAction.toPerm g

theorem actionPermutation_apply (g : G) (x : X) : actionPermutation g x = g • x := rfl

/-- The fixed-point set of an element. -/
def fixedPointSet (g : G) : Set X := Function.fixedPoints (actionPermutation g)

theorem mem_fixedPointSet_iff (g : G) (x : X) :
    x ∈ fixedPointSet (X := X) g ↔ g • x = x := Iff.rfl

/-- The subgroup fixing a point. -/
abbrev pointStabilizer (x : X) : Subgroup G := MulAction.stabilizer G x

theorem mem_pointStabilizer_iff (x : X) (g : G) :
    g ∈ pointStabilizer (G := G) x ↔ g • x = x := Iff.rfl

/-- The orbit of a point. -/
abbrev pointOrbit (x : X) : Set X := MulAction.orbit G x

theorem mem_pointOrbit_iff (x y : X) :
    y ∈ pointOrbit (G := G) x ↔ ∃ g : G, g • x = y := MulAction.mem_orbit_iff

/-- left cosets of a stabilizer parametrize the orbit. -/
noncomputable def orbitCosetEquivalence (x : X) :
    (G ⧸ pointStabilizer (G := G) x) ≃ pointOrbit (G := G) x :=
  (MulAction.orbitEquivQuotientStabilizer G x).symm

/-- The coset of `g` corresponds to the point `g • x`. -/
theorem orbitCosetEquivalence_apply (x : X) (g : G) :
    (orbitCosetEquivalence x (QuotientGroup.mk g) : X) = g • x :=
  MulAction.orbitEquivQuotientStabilizer_symm_apply G x g

/-- A left coset is exactly the set of elements carrying `x` to the same orbit point. -/
theorem action_fiber_eq_leftCoset (x : X) (h : G) :
    (fun g : G => g • x) ⁻¹' {h • x} = h • (pointStabilizer (G := G) x : Set G) := by
  ext g
  rw [Set.mem_preimage, Set.mem_singleton_iff, mem_leftCoset_iff]
  change g • x = h • x ↔ (h⁻¹ * g) • x = x
  constructor
  · intro hx
    rw [mul_smul, hx, inv_smul_smul]
  · intro hx
    simpa [smul_smul, mul_assoc] using congrArg (fun y => h • y) hx

/-- The subgroup obtained by conjugating by the given element. -/
def subgroupConjugate (h : G) (K : Subgroup G) : Subgroup G :=
  K.map (MulAut.conj h).toMonoidHom

/-- two subgroups are conjugate in the ambient group. -/
def AreConjugateSubgroups (K L : Subgroup G) : Prop :=
  ∃ h : G, K = subgroupConjugate h L

theorem mem_subgroupConjugate_iff (h : G) (K : Subgroup G) (g : G) :
    g ∈ subgroupConjugate h K ↔ ∃ k ∈ K, h * k * h⁻¹ = g := Iff.rfl

/-- Conjugate subgroups are isomorphic by restriction of the inner automorphism. -/
def subgroupConjugateEquivalence (h : G) (K : Subgroup G) :
    K ≃* subgroupConjugate h K := (MulAut.conj h).subgroupMap K

/-- The subgroup conjugacy relation implies isomorphism. -/
theorem conjugateSubgroups_isomorphic {K L : Subgroup G}
    (hKL : AreConjugateSubgroups K L) : Nonempty (K ≃* L) := by
  obtain ⟨h, rfl⟩ := hKL
  exact ⟨(subgroupConjugateEquivalence h L).symm⟩

/-- conjugation transports the fixed-point set. -/
theorem fixedPointSet_conjugate (h g : G) :
    fixedPointSet (X := X) (h * g * h⁻¹) =
      (fun x : X => h • x) '' fixedPointSet (X := X) g := by
  ext y
  constructor
  · intro hy
    refine ⟨h⁻¹ • y, ?_, by simp⟩
    change (h * g * h⁻¹) • y = y at hy
    change g • h⁻¹ • y = h⁻¹ • y
    simpa [smul_smul, mul_assoc] using congrArg (fun x => h⁻¹ • x) hy
  · rintro ⟨x, hx, rfl⟩
    change g • x = x at hx
    change (h * g * h⁻¹) • (h • x) = h • x
    simpa [smul_smul, mul_assoc] using congrArg (fun y => h • y) hx

/-- stabilizers of translated points are conjugate subgroups. -/
theorem stabilizer_conjugation (h : G) (x : X) :
    pointStabilizer (G := G) (h • x) = subgroupConjugate h (pointStabilizer (G := G) x) :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj h x

/-- Points in the same orbit have conjugate stabilizers. -/
theorem stabilizers_conjugate_of_same_orbit (x y : X)
    (hy : y ∈ pointOrbit (G := G) x) :
    AreConjugateSubgroups (pointStabilizer (G := G) y) (pointStabilizer (G := G) x) := by
  obtain ⟨h, rfl⟩ := (mem_pointOrbit_iff x y).mp hy
  exact ⟨h, stabilizer_conjugation h x⟩

/-- equation: commuting elements preserve each other's fixed points. -/
theorem commuting_fixedPointSet_image {g h : G} (hc : Commute g h) :
    (fun x : X => g • x) '' fixedPointSet (X := X) h = fixedPointSet (X := X) h := by
  have he : g * h * g⁻¹ = h := by rw [hc.eq]; simp [mul_assoc]
  rw [← fixedPointSet_conjugate, he]

/-- Both fixed-point-set equalities for the actual action. -/
theorem commuting_preserve_fixedPointSets {g h : G} (hc : Commute g h) :
    ((fun x : X => g • x) '' fixedPointSet (X := X) h = fixedPointSet (X := X) h) ∧
      ((fun x : X => h • x) '' fixedPointSet (X := X) g = fixedPointSet (X := X) g) :=
  ⟨commuting_fixedPointSet_image hc, commuting_fixedPointSet_image hc.symm⟩

end LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions
