/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Mobius.FractionalLinear
public import LowDimensionalTopology.Geometry.Inversive.Inversions
public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Mathlib.Tactic

/-!
# The upper-half-space quaternion coordinates

The subspace of quaternions with vanishing k coordinate inherits its Euclidean
metric and is linearly isometric to real three-space. Positive j coordinate
defines H3. Its actual topological boundary in the one-point compactification
is identified homeomorphically with the extended complex plane.
-/

@[expose] public section

namespace LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

noncomputable section

open scoped Quaternion OnePoint
open Set Topology Filter

/-- The genuine Euclidean three-space inside the quaternions: the k coefficient vanishes. -/
def quaternionThreeSpace : Submodule ℝ ℍ where
  carrier := {q | q.imK = 0}
  zero_mem' := rfl
  add_mem' := by
    intro a b ha hb
    change a.imK = 0 at ha
    change b.imK = 0 at hb
    change a.imK + b.imK = 0
    rw [ha, hb, add_zero]
  smul_mem' := by
    intro a b hb
    change b.imK = 0 at hb
    change a * b.imK = 0
    rw [hb, mul_zero]

@[simp] theorem mem_quaternionThreeSpace (q : ℍ) :
    q ∈ quaternionThreeSpace ↔ q.imK = 0 := Iff.rfl

/-- Complex-horizontal coordinate in the quaternion model of three-space. -/
def quaternionHorizontal (q : quaternionThreeSpace) : ℂ := ⟨q.val.re, q.val.imI⟩

/-- Vertical coordinate in the quaternion model of three-space. -/
def quaternionHeight (q : quaternionThreeSpace) : ℝ := q.val.imJ

/-- The point with horizontal coordinate z and signed vertical coordinate t. -/
def quaternionThreePoint (z : ℂ) (t : ℝ) : quaternionThreeSpace :=
  ⟨⟨z.re, z.im, t, 0⟩, rfl⟩

@[simp] theorem quaternionHorizontal_threePoint (z : ℂ) (t : ℝ) :
    quaternionHorizontal (quaternionThreePoint z t) = z := by
  apply Complex.ext <;> rfl

@[simp] theorem quaternionHeight_threePoint (z : ℂ) (t : ℝ) :
    quaternionHeight (quaternionThreePoint z t) = t := rfl

@[simp] theorem quaternionThreePoint_coordinates (q : quaternionThreeSpace) :
    quaternionThreePoint (quaternionHorizontal q) (quaternionHeight q) = q := by
  apply Subtype.ext
  apply Quaternion.ext <;> simp [quaternionThreePoint, quaternionHorizontal,
    quaternionHeight]
  exact q.property.symm

/-- The source's symbol j is the actual quaternion basis vector. -/
def quaternionJ : ℍ := ⟨0, 0, 1, 0⟩

/-- uses the actual quaternion sum z+t j. -/
theorem quaternionThreePoint_quaternion (z : ℂ) (t : ℝ) :
    (quaternionThreePoint z t : ℍ) = (z : ℍ) + t • quaternionJ := by
  apply Quaternion.ext <;> simp [quaternionThreePoint, quaternionJ]

/-- Three real Euclidean coordinates and the quaternion three-space are linearly isometric. -/
def euclideanThreeQuaternion : Inversive.Euclidean 3 ≃ₗᵢ[ℝ] quaternionThreeSpace :=
  { toFun := fun x => ⟨⟨x 0, x 1, x 2, 0⟩, rfl⟩
    invFun := fun q => WithLp.toLp 2 ![q.val.re, q.val.imI, q.val.imJ]
    map_add' := by intro x y; apply Subtype.ext; apply Quaternion.ext <;> first | rfl | simp
    map_smul' := by intro r x; apply Subtype.ext; apply Quaternion.ext <;> first | rfl | simp
    left_inv := by
      intro x
      apply WithLp.ofLp_injective
      funext i
      fin_cases i <;> rfl
    right_inv := by
      intro q
      apply Subtype.ext
      apply Quaternion.ext <;> first | rfl | exact q.property.symm
    norm_map' := by
      intro x
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change ‖(⟨x 0, x 1, x 2, 0⟩ : ℍ)‖ ^ 2 = ‖x‖ ^ 2
      rw [EuclideanSpace.real_norm_sq_eq, pow_two, ← Quaternion.normSq_eq_norm_mul_self]
      simp [Quaternion.normSq_def', Fin.sum_univ_three] }

@[simp] theorem euclideanThreeQuaternion_horizontal (x : Inversive.Euclidean 3) :
    quaternionHorizontal (euclideanThreeQuaternion x) = ⟨x 0, x 1⟩ := rfl

@[simp] theorem euclideanThreeQuaternion_height (x : Inversive.Euclidean 3) :
    quaternionHeight (euclideanThreeQuaternion x) = x 2 := rfl

/-- The model uses the inherited Euclidean distance, rather than a newly chosen metric. -/
theorem euclideanThreeQuaternion_dist (x y : Inversive.Euclidean 3) :
    dist (euclideanThreeQuaternion x) (euclideanThreeQuaternion y) = dist x y :=
  euclideanThreeQuaternion.dist_map x y

/-- The same genuine Euclidean identification extends to the shared point at infinity. -/
def extendedEuclideanThreeQuaternion :
    OnePoint (Inversive.Euclidean 3) ≃ₜ OnePoint quaternionThreeSpace :=
  euclideanThreeQuaternion.toHomeomorph.onePointCongr

/-- H3 consists of precisely the positive-height points of the quaternion Euclidean space. -/
def upperHalfSpaceSet : Set quaternionThreeSpace := {q | 0 < quaternionHeight q}

/-- The upper-half-space model, before equipping it with its hyperbolic metric. -/
abbrev UpperHalfSpace := upperHalfSpaceSet

/-- A point of H3 constructed from its complex horizontal coordinate and positive height. -/
def upperHalfSpacePoint (z : ℂ) (t : ℝ) (ht : 0 < t) : UpperHalfSpace :=
  ⟨quaternionThreePoint z t, ht⟩

@[simp] theorem upperHalfSpacePoint_horizontal (z : ℂ) (t : ℝ) (ht : 0 < t) :
    quaternionHorizontal (upperHalfSpacePoint z t ht).val = z :=
  quaternionHorizontal_threePoint z t

@[simp] theorem upperHalfSpacePoint_height (z : ℂ) (t : ℝ) (ht : 0 < t) :
    quaternionHeight (upperHalfSpacePoint z t ht).val = t := rfl

/-- The distinguished point j has horizontal coordinate zero and height one. -/
def upperHalfSpaceJ : UpperHalfSpace := upperHalfSpacePoint 0 1 zero_lt_one

@[simp] theorem upperHalfSpaceJ_horizontal : quaternionHorizontal upperHalfSpaceJ.val = 0 := by
  simp [upperHalfSpaceJ]

@[simp] theorem upperHalfSpaceJ_height : quaternionHeight upperHalfSpaceJ.val = 1 := rfl

/-- Every positive-height point has the source's unique z+t j coordinates. -/
theorem upperHalfSpace_coordinates (q : UpperHalfSpace) :
    upperHalfSpacePoint (quaternionHorizontal q.val) (quaternionHeight q.val) q.property = q := by
  apply Subtype.ext
  exact quaternionThreePoint_coordinates q.val

/-- The horizontal boundary subspace inherits the actual Euclidean metric. -/
def quaternionBoundarySpace : Submodule ℝ quaternionThreeSpace where
  carrier := {q | quaternionHeight q = 0}
  zero_mem' := rfl
  add_mem' := by
    intro a b ha hb
    change quaternionHeight a + quaternionHeight b = 0
    rw [show quaternionHeight a = 0 from ha, show quaternionHeight b = 0 from hb, add_zero]
  smul_mem' := by intro a b hb; change a * b.val.imJ = 0; rw [show b.val.imJ = 0 from hb, mul_zero]

/-- The actual complex plane is linearly isometric to the zero-height boundary plane. -/
def complexQuaternionBoundary : ℂ ≃ₗᵢ[ℝ] quaternionBoundarySpace :=
  { toFun := fun z => ⟨quaternionThreePoint z 0, rfl⟩
    invFun := fun q => quaternionHorizontal q.val
    map_add' := by
      intro z w
      apply Subtype.ext
      apply Subtype.ext
      apply Quaternion.ext <;> simp [quaternionThreePoint]
    map_smul' := by
      intro r z
      apply Subtype.ext
      apply Subtype.ext
      apply Quaternion.ext <;> simp [quaternionThreePoint]
    left_inv := fun z => quaternionHorizontal_threePoint z 0
    right_inv := by
      intro q
      apply Subtype.ext
      have h := quaternionThreePoint_coordinates q.val
      rw [show quaternionHeight q.val = 0 from q.property] at h
      exact h
    norm_map' := by
      intro z
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change ‖(quaternionThreePoint z 0 : ℍ)‖ ^ 2 = ‖z‖ ^ 2
      rw [Complex.sq_norm, pow_two, ← Quaternion.normSq_eq_norm_mul_self]
      simp [quaternionThreePoint, Quaternion.normSq_def', Complex.normSq_apply, pow_two] }

/-- Height is a genuine continuous real-linear functional on the Euclidean ambient space. -/
def quaternionHeightLinear : quaternionThreeSpace →ₗ[ℝ] ℝ where
  toFun := quaternionHeight
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def quaternionHeightContinuous : quaternionThreeSpace →L[ℝ] ℝ :=
  quaternionHeightLinear.toContinuousLinearMap

@[simp] theorem quaternionHeightContinuous_apply (q : quaternionThreeSpace) :
    quaternionHeightContinuous q = quaternionHeight q := rfl

theorem quaternionHeight_surjective : Function.Surjective quaternionHeightContinuous :=
  fun t => ⟨quaternionThreePoint 0 t, rfl⟩

theorem isOpen_upperHalfSpaceSet : IsOpen upperHalfSpaceSet :=
  isOpen_Ioi.preimage quaternionHeightContinuous.continuous

/-- The finite boundary of H3 is exactly the horizontal complex plane. -/
theorem frontier_upperHalfSpaceSet :
    frontier upperHalfSpaceSet = (quaternionBoundarySpace : Set quaternionThreeSpace) := by
  change frontier (quaternionHeightContinuous ⁻¹' Set.Ioi 0) = _
  rw [quaternionHeightContinuous.frontier_preimage quaternionHeight_surjective, frontier_Ioi]
  rfl

/-- Adding the same point at infinity gives the geometric extended complex boundary plane. -/
def extendedComplexQuaternionBoundary : OnePoint ℂ ≃ₜ OnePoint quaternionBoundarySpace :=
  complexQuaternionBoundary.toHomeomorph.onePointCongr

/-- The complex plane embedded isometrically in the actual three-dimensional ambient space. -/
def complexQuaternionPlane : ℂ →ₗᵢ[ℝ] quaternionThreeSpace :=
  quaternionBoundarySpace.subtypeₗᵢ.comp complexQuaternionBoundary.toLinearIsometry

@[simp] theorem complexQuaternionPlane_apply (z : ℂ) :
    complexQuaternionPlane z = quaternionThreePoint z 0 := rfl

theorem range_complexQuaternionPlane :
    Set.range complexQuaternionPlane = (quaternionBoundarySpace : Set quaternionThreeSpace) := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    rfl
  · intro hq
    refine ⟨quaternionHorizontal q, ?_⟩
    change quaternionThreePoint (quaternionHorizontal q) 0 = q
    simpa only [show quaternionHeight q = 0 from hq] using quaternionThreePoint_coordinates q

/-- The same embedding with the single shared point at infinity. -/
def extendedBoundaryEmbedding : OnePoint ℂ → OnePoint quaternionThreeSpace :=
  OnePoint.map complexQuaternionPlane

@[simp] theorem extendedBoundaryEmbedding_infty : extendedBoundaryEmbedding ∞ = ∞ := rfl

@[simp] theorem extendedBoundaryEmbedding_coe (z : ℂ) :
    extendedBoundaryEmbedding z = (quaternionThreePoint z 0 : OnePoint quaternionThreeSpace) := rfl

/-- The boundary embedding is continuous at infinity because its Euclidean embedding is proper. -/
theorem continuous_extendedBoundaryEmbedding : Continuous extendedBoundaryEmbedding := by
  apply OnePoint.continuous_map complexQuaternionPlane.continuous
  rw [coclosedCompact_eq_cocompact, coclosedCompact_eq_cocompact]
  exact (isProperMap_iff_tendsto_cocompact.mp
    complexQuaternionPlane.isometry.isClosedEmbedding.isProperMap).2

theorem injective_extendedBoundaryEmbedding : Function.Injective extendedBoundaryEmbedding := by
  intro z w h
  induction z using OnePoint.rec <;> induction w using OnePoint.rec
  · rfl
  · simp at h
  · simp at h
  · have hq : quaternionThreePoint _ 0 = quaternionThreePoint _ 0 :=
      OnePoint.coe_injective h
    have hh := congrArg quaternionHorizontal hq
    apply congrArg OnePoint.some
    simpa only [quaternionHorizontal_threePoint] using hh

/-- H3 as a subset of the actual one-point compactification of Euclidean three-space. -/
def extendedUpperHalfSpaceSet : Set (OnePoint quaternionThreeSpace) :=
  ((↑) : quaternionThreeSpace → OnePoint quaternionThreeSpace) '' upperHalfSpaceSet

theorem isOpen_extendedUpperHalfSpaceSet : IsOpen extendedUpperHalfSpaceSet :=
  OnePoint.isOpen_image_coe.mpr isOpen_upperHalfSpaceSet

/-- Infinity really is a limit point of H3, rather than an isolated added boundary symbol. -/
theorem infty_mem_closure_extendedUpperHalfSpaceSet :
    (∞ : OnePoint quaternionThreeSpace) ∈ closure extendedUpperHalfSpaceSet := by
  by_contra h
  have hc : IsCompact (((↑) : quaternionThreeSpace → OnePoint quaternionThreeSpace) ⁻¹'
      closure extendedUpperHalfSpaceSet) :=
    ((OnePoint.isClosed_iff_of_notMem h).mp isClosed_closure).2
  obtain ⟨R, hR⟩ := (hc.image quaternionHeightContinuous.continuous).bddAbove
  let t := max R 0 + 1
  have ht : 0 < t := by dsimp [t]; linarith [le_max_right R 0]
  have hq : (quaternionThreePoint 0 t : OnePoint quaternionThreeSpace) ∈
      closure extendedUpperHalfSpaceSet :=
    subset_closure ⟨quaternionThreePoint 0 t, ht, rfl⟩
  have hbound := hR ⟨quaternionThreePoint 0 t, hq, rfl⟩
  change t ≤ R at hbound
  dsimp [t] at hbound
  linarith [le_max_left R 0]

/-- The complete topological boundary is the finite zero-height plane and infinity. -/
theorem frontier_extendedUpperHalfSpaceSet :
    frontier extendedUpperHalfSpaceSet = insert ∞
      (((↑) : quaternionThreeSpace → OnePoint quaternionThreeSpace) ''
        (quaternionBoundarySpace : Set quaternionThreeSpace)) := by
  have hf := OnePoint.isOpenMap_coe.preimage_frontier_eq_frontier_preimage
    (X := quaternionThreeSpace) OnePoint.continuous_coe extendedUpperHalfSpaceSet
  have hpre : ((↑) : quaternionThreeSpace → OnePoint quaternionThreeSpace) ⁻¹'
      frontier extendedUpperHalfSpaceSet = frontier upperHalfSpaceSet := by
    simpa only [extendedUpperHalfSpaceSet, Set.preimage_image_eq _ OnePoint.coe_injective]
      using hf
  ext q
  induction q using OnePoint.rec with
  | infty =>
    simp only [Set.mem_insert_iff, true_or, iff_true]
    rw [frontier, isOpen_extendedUpperHalfSpaceSet.interior_eq]
    exact ⟨infty_mem_closure_extendedUpperHalfSpaceSet, OnePoint.infty_notMem_image_coe⟩
  | coe q =>
    have hq : ((q : OnePoint quaternionThreeSpace) ∈ frontier extendedUpperHalfSpaceSet) ↔
        q ∈ (quaternionBoundarySpace : Set quaternionThreeSpace) := by
      change q ∈ ((↑) : quaternionThreeSpace → OnePoint quaternionThreeSpace) ⁻¹'
        frontier extendedUpperHalfSpaceSet ↔ _
      rw [hpre, frontier_upperHalfSpaceSet]
    simpa only [Set.mem_insert_iff, OnePoint.coe_ne_infty, false_or,
      Set.mem_image, OnePoint.some_eq_iff, exists_eq_right] using hq

/-- The extended complex plane lands on the entire boundary, including infinity. -/
theorem range_extendedBoundaryEmbedding :
    Set.range extendedBoundaryEmbedding = frontier extendedUpperHalfSpaceSet := by
  rw [frontier_extendedUpperHalfSpaceSet]
  ext q
  induction q using OnePoint.rec with
  | infty =>
    simp only [Set.mem_insert_iff, true_or, iff_true]
    exact ⟨∞, rfl⟩
  | coe q =>
    constructor
    · rintro ⟨z, hz⟩
      induction z using OnePoint.rec with
      | infty => simp at hz
      | coe z =>
        simp only [extendedBoundaryEmbedding_coe, OnePoint.some_eq_iff] at hz
        exact Set.mem_insert_of_mem _ ⟨quaternionThreePoint z 0, rfl, congrArg OnePoint.some hz⟩
    · intro hq
      have hq' : q ∈ (quaternionBoundarySpace : Set quaternionThreeSpace) := by
        simpa only [Set.mem_insert_iff, OnePoint.coe_ne_infty, false_or,
          Set.mem_image, OnePoint.some_eq_iff, exists_eq_right] using hq
      obtain ⟨z, hz⟩ := range_complexQuaternionPlane.symm ▸ hq'
      exact ⟨z, congrArg OnePoint.some hz⟩

/--
The boundary of H3 in extended Euclidean three-space is the extended complex
plane, with its genuine one-point-compactification topology.
-/
def extendedComplexUpperHalfSpaceBoundary :
    OnePoint ℂ ≃ₜ frontier extendedUpperHalfSpaceSet :=
  (continuous_extendedBoundaryEmbedding.isClosedEmbedding
    injective_extendedBoundaryEmbedding).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr range_extendedBoundaryEmbedding)

@[simp] theorem extendedComplexUpperHalfSpaceBoundary_apply (z : OnePoint ℂ) :
    (extendedComplexUpperHalfSpaceBoundary z : OnePoint quaternionThreeSpace) =
      extendedBoundaryEmbedding z := rfl

end
end LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
