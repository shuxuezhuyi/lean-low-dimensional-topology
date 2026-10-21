/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FiniteOrbit
public import LowDimensionalTopology.Geometry.Mobius.InvariantDisc.InvariantDiscConverse
public import Mathlib.GroupTheory.CosetCover
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic.Push
@[expose] public section
noncomputable section
open Set
open scoped OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Infinite point orbits allow a finite set to be translated away from any other finite set. -/
theorem exists_disjoint_translate_of_infinite_orbits {G X : Type*} [Group G] [MulAction G X]
    (hOrb : ∀ x : X, (MulAction.orbit G x).Infinite) (F S : Finset X) :
    ∃ g : G, Disjoint ((fun x => g • x) '' (F : Set X)) (S : Set X) := by
  classical
  by_contra h
  push Not at h
  let a : X × X → G := fun p =>
    if hp : ∃ g : G, g • p.1 = p.2 then hp.choose else 1
  have ha (p : X × X) (hp : ∃ g : G, g • p.1 = p.2) : a p • p.1 = p.2 := by
    simp only [a, dite_eq_left hp]
    exact hp.choose_spec
  have hcover : ⋃ p ∈ F.product S, a p • (MulAction.stabilizer G p.1 : Set G) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := Set.not_disjoint_iff.mp (h g)
    apply Set.mem_iUnion_of_mem (x, g • x)
    apply Set.mem_iUnion_of_mem (Finset.mem_product.mpr ⟨hx, hy⟩)
    rw [mem_leftCoset_iff]
    change ((a (x, g • x))⁻¹ * g) • x = x
    rw [mul_smul]
    exact inv_smul_eq_iff.mpr (ha (x, g • x) ⟨g, rfl⟩).symm
  obtain ⟨p, _, hp⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcover
  let stabilizerFiniteIndex : (MulAction.stabilizer G p.1).FiniteIndex := hp
  let orbitFinite : Finite (MulAction.orbit G p.1) :=
    Finite.of_equiv (G ⧸ MulAction.stabilizer G p.1)
      (MulAction.orbitEquivQuotientStabilizer G p.1).symm
  exact hOrb p.1 (Set.toFinite _)

/-- A set-based version of the finite-translate avoidance lemma. -/
theorem exists_disjoint_translate_of_finite_sets {G X : Type*} [Group G] [MulAction G X]
    (hOrb : ∀ x : X, (MulAction.orbit G x).Infinite) {F S : Set X}
    (hF : F.Finite) (hS : S.Finite) :
    ∃ g : G, Disjoint ((fun x => g • x) '' F) S := by
  simpa only [Set.Finite.coe_toFinset] using
    exists_disjoint_translate_of_infinite_orbits hOrb hF.toFinset hS.toFinset

/-- Repeated finite avoidance constructs a sequence of pairwise disjoint translates. -/
theorem exists_pairwise_disjoint_translates_of_infinite_orbits
    {G X : Type*} [Group G] [MulAction G X]
    (hOrb : ∀ x : X, (MulAction.orbit G x).Infinite) (F : Finset X) :
    ∃ u : ℕ → G, Pairwise (fun i j =>
      Disjoint ((fun x => u i • x) '' (F : Set X)) ((fun x => u j • x) '' (F : Set X))) := by
  classical
  let t : Finset X → G := fun S => (exists_disjoint_translate_of_infinite_orbits hOrb F S).choose
  have ht (S : Finset X) : Disjoint ((fun x => t S • x) '' (F : Set X)) (S : Set X) :=
    (exists_disjoint_translate_of_infinite_orbits hOrb F S).choose_spec
  let A : ℕ → Finset X := Nat.rec ∅ (fun _ S => S ∪ F.image (fun x => t S • x))
  have hsucc (n : ℕ) : A (n + 1) = A n ∪ F.image (fun x => t (A n) • x) := rfl
  have hmono : Monotone A := monotone_nat_of_le_succ (fun n => by
    rw [hsucc]
    exact Finset.subset_union_left)
  let u : ℕ → G := fun n => t (A n)
  have hprev (i j : ℕ) (hij : i < j) :
      ((fun x => u i • x) '' (F : Set X)) ⊆ {x : X | x ∈ A j} := by
    intro x hx
    have hx' : x ∈ F.image (fun y => t (A i) • y) := by
      rcases hx with ⟨y, hy, rfl⟩
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    have hxstep : x ∈ A (i + 1) := by
      rw [hsucc]
      exact Finset.mem_union.mpr (Or.inr hx')
    exact hmono (Nat.succ_le_iff.mpr hij) hxstep
  have hlt (i j : ℕ) (hij : i < j) :
      Disjoint ((fun x => u i • x) '' (F : Set X)) ((fun x => u j • x) '' (F : Set X)) :=
    ((ht (A j)).mono_right (hprev i j hij)).symm
  refine ⟨u, fun i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact (hlt j i h).symm

/-- The disjoint-translate sequence for an arbitrary finite set. -/
theorem exists_pairwise_disjoint_translates_of_finite_set
    {G X : Type*} [Group G] [MulAction G X]
    (hOrb : ∀ x : X, (MulAction.orbit G x).Infinite) {F : Set X} (hF : F.Finite) :
    ∃ u : ℕ → G, Pairwise (fun i j =>
      Disjoint ((fun x => u i • x) '' F) ((fun x => u j • x) '' F)) := by
  simpa only [Set.Finite.coe_toFinset] using
    exists_pairwise_disjoint_translates_of_infinite_orbits hOrb hF.toFinset

/-- For a nonempty finite set the translating group elements can be chosen pairwise distinct. -/
theorem exists_injective_pairwise_disjoint_translates
    {G X : Type*} [Group G] [MulAction G X]
    (hOrb : ∀ x : X, (MulAction.orbit G x).Infinite) (F : Finset X) (hF : F.Nonempty) :
    ∃ u : ℕ → G, Function.Injective u ∧ Pairwise (fun i j =>
      Disjoint ((fun x => u i • x) '' (F : Set X)) ((fun x => u j • x) '' (F : Set X))) := by
  obtain ⟨u, hu⟩ := exists_pairwise_disjoint_translates_of_infinite_orbits hOrb F
  refine ⟨u, ?_, hu⟩
  intro i j he
  by_contra hij
  obtain ⟨x, hx⟩ := hF
  apply Set.disjoint_left.mp (hu hij)
  · exact ⟨x, hx, rfl⟩
  · exact ⟨x, hx, by rw [he]⟩


/-- The first step, using the established actual hyperbolic/strictly-loxodromic dichotomy. -/
theorem nonElementary_exists_loxodromic (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) : ∃ f ∈ H, Mobius.MobiusLoxodromic f := by
  by_cases hns : ∀ f : H, ¬Mobius.MobiusStrictlyLoxodromic f.val
  · obtain ⟨f, hf, hhyper⟩ := hH.exists_hyperbolic_of_noStrictlyLoxodromic hns
    exact ⟨f, hf, hhyper.1⟩
  · push Not at hns
    obtain ⟨f, hf⟩ := hns
    exact ⟨f.val, f.property, hf.1⟩

/-- All actual boundary orbits of a non-elementary group are infinite. -/
theorem nonElementary_boundary_orbit_infinite (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (z : Mobius.ExtendedComplex) : (MulAction.orbit H z).Infinite := by
  intro hz
  exact hH ((isElementary_iff_boundary_or_interior H).mpr (Or.inl ⟨z, hz⟩))



local instance nonElementaryQuaternionMulAction :
    MulAction Mobius.complexMobiusGroup (OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :=
  MulAction.compHom (OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) Mobius.mobiusExtendedSpaceHom

/-- The quaternion compactification identification intertwines the genuine full-space action. -/
theorem nonElementaryQuaternion_equivariant (f : Mobius.complexMobiusGroup)
    (x : Inversive.ExtendedEuclidean 3) :
    Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion (f • x) = f •
      Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion x := by
  change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion ((Mobius.mobiusGeometricPoincareHom f :
    Inversive.ExtendedHomeomorph 3) x) =
    Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion ((Mobius.mobiusGeometricPoincareHom f :
      Inversive.ExtendedHomeomorph 3)
      (Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.symm
        (Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion x)))
  rw [Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.symm_apply_apply]

/-- Non-elementarity makes every orbit in the entire quaternion compactification infinite. -/
theorem nonElementary_quaternion_orbit_infinite (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (q : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    (MulAction.orbit H q).Infinite := by
  intro hq
  have hf : DiscreteGroups.Action.HasFiniteOrbit H (OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)
    := ⟨q, hq⟩
  have hn : DiscreteGroups.Action.HasFiniteOrbit H (Inversive.ExtendedEuclidean 3) :=
    (DiscreteGroups.Action.hasFiniteOrbit_equivariant_iff
      Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.toEquiv
      (fun (f : H) x => nonElementaryQuaternion_equivariant f.val x)).mp hf
  exact hH ((isElementary_iff_compactified_finite_orbit H).mpr hn)

/-- A genuine loxodromic map has a finite nonempty full-space fixed-point set. -/
theorem loxodromic_full_fixedPoints_finite_nonempty {f : Mobius.complexMobiusGroup}
    (hf : Mobius.MobiusLoxodromic f) :
    (Mobius.mobiusExtendedFixedPoints f).Finite ∧ (Mobius.mobiusExtendedFixedPoints f).Nonempty := by
  obtain ⟨a, b, _, hfix⟩ := hf.2
  constructor
  · apply ((Set.finite_singleton b).insert a).subset
    intro q hq
    simpa only [mem_insert_iff, mem_singleton_iff] using (hfix q).mp hq
  · exact ⟨a, (hfix a).mpr (Or.inl rfl)⟩

/-- With disjoint fixed sets in the entire compactified three-space. -/
theorem exists_injective_loxodromic_sequence_pairwise_disjoint_fixedPoints (H : Subgroup
    Mobius.complexMobiusGroup) (hH : IsNonElementary H) :
    ∃ a : ℕ → H, Function.Injective a ∧ (∀ n, Mobius.MobiusLoxodromic (a n).val) ∧
      Pairwise (fun m n => Disjoint (Mobius.mobiusExtendedFixedPoints (a m).val)
        (Mobius.mobiusExtendedFixedPoints (a n).val)) := by
  obtain ⟨f, hfH, hfL⟩ := nonElementary_exists_loxodromic H hH
  let fH : H := ⟨f, hfH⟩
  let F := Mobius.mobiusExtendedFixedPoints f
  obtain ⟨hfinite, _⟩ := loxodromic_full_fixedPoints_finite_nonempty hfL
  obtain ⟨u, hu⟩ := exists_pairwise_disjoint_translates_of_finite_set
    (nonElementary_quaternion_orbit_infinite H hH) hfinite
  let a : ℕ → H := fun n => u n * fH * (u n)⁻¹
  have haval (n : ℕ) : (a n).val = (u n).val * f * (u n).val⁻¹ := rfl
  have hL (n : ℕ) : Mobius.MobiusLoxodromic (a n).val := by
    rw [haval]
    exact Mobius.mobiusLoxodromic_conjugation_forward f (u n).val hfL
  have hF (n : ℕ) : Mobius.mobiusExtendedFixedPoints (a n).val =
      (fun q : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace => u n • q) '' F := by
    rw [haval, Mobius.mobiusExtendedFixedPoints_conjugation]
    rfl
  have hpair : Pairwise (fun m n => Disjoint (Mobius.mobiusExtendedFixedPoints (a m).val)
      (Mobius.mobiusExtendedFixedPoints (a n).val)) := by
    intro m n hmn
    rw [hF, hF]
    exact hu hmn
  refine ⟨a, ?_, hL, hpair⟩
  intro m n heq
  by_contra hmn
  obtain ⟨q, hq⟩ := (loxodromic_full_fixedPoints_finite_nonempty (hL m)).2
  have hqn := hq
  rw [heq] at hqn
  exact Set.disjoint_left.mp (hpair hmn) hq hqn

end LowDimensionalTopology.Geometry.DiscreteGroups
