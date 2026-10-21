module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Path

/-!
# Extending a path by integer group translates.

A path from a point to its image under a group element extends to the real line by
integer powers of that element. A locally finite cover by consecutive unit intervals
gives continuity, and translation by one agrees with the group action.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped Pointwise unitInterval

namespace LowDimensionalTopology.Geometry.DiscreteGroups.Action

/-- The actual consecutive compact integer intervals used to glue the developed curve. -/
def pathExtensionInterval (n : ℤ) : Set ℝ := Icc (n : ℝ) ((n : ℝ) + 1)

theorem pathExtensionInterval_cover : (⋃ n : ℤ, pathExtensionInterval n) = univ := by
  apply eq_univ_of_forall
  intro t
  exact mem_iUnion.mpr ⟨⌊t⌋,Int.floor_le t,(Int.lt_floor_add_one t).le⟩

theorem pathExtensionInterval_locallyFinite : LocallyFinite pathExtensionInterval := by
  apply locallyFinite_Icc_of_tendsto
  · exact tendsto_intCast_atTop_atTop
  · exact tendsto_atBot_add_const_right _ 1 (tendsto_intCast_atBot_iff.mpr tendsto_id)

/-- Consecutive actual group translates of a genuine path agree on their actual
integer-interval overlaps, including their common endpoints. -/
theorem equivariantPathExtension_overlap {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (g : G) {x : X} (γ : Path x (g • x))
    (n m : ℤ) (t : ℝ) (hn : t ∈ pathExtensionInterval n)
    (hm : t ∈ pathExtensionInterval m) :
    g^n • γ.extend (t-(n:ℝ)) = g^m • γ.extend (t-(m:ℝ)) := by
  have hle (n m : ℤ) (hnm : n ≤ m) (hn : t ∈ pathExtensionInterval n)
      (hm : t ∈ pathExtensionInterval m) :
      g^n • γ.extend (t-(n:ℝ)) = g^m • γ.extend (t-(m:ℝ)) := by
    by_cases he : n = m
    · rw [he]
    · have hstep : n+1 ≤ m := by omega
      have hstepR : (n:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast hstep
      have htm : t = (m:ℝ) := by
        have hn' : t ≤ (n:ℝ)+1 := hn.2
        have hm' : (m:ℝ) ≤ t := hm.1
        linarith
      have hmnR : (m:ℝ) = (n:ℝ)+1 := by
        have hn' : t ≤ (n:ℝ)+1 := hn.2
        linarith
      have hmn : m = n+1 := by exact_mod_cast hmnR
      have htn : t-(n:ℝ) = 1 := by linarith
      rw [htn,htm,sub_self,Path.extend_one,Path.extend_zero,hmn,zpow_add,zpow_one,mul_smul]
  rcases le_total n m with hnm | hmn
  · exact hle n m hnm hn hm
  · exact (hle m n hmn hm hn).symm

/-- The genuine real-parameter curve obtained by gluing all integer translates of
an actual path from a point to its actual group translate. -/
def equivariantPathExtension {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (g : G) {x : X} (γ : Path x (g • x)) : ℝ → X :=
  Set.liftCover pathExtensionInterval
    (fun n t => g^n • γ.extend (t.val-(n:ℝ)))
    (equivariantPathExtension_overlap g γ) pathExtensionInterval_cover

/-- On every actual compact integer interval, the extension equals the corresponding
actual translate of the original path, including both endpoints. -/
theorem equivariantPathExtension_on_interval {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (g : G) {x : X} (γ : Path x (g • x))
    (n : ℤ) {t : ℝ} (ht : t ∈ pathExtensionInterval n) :
    equivariantPathExtension g γ t = g^n • γ.extend (t-(n:ℝ)) :=
  Set.liftCover_of_mem ht

/-- Local finiteness of the genuine compact interval cover proves actual global
continuity of the entire developed real-parameter curve. -/
theorem continuous_equivariantPathExtension {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    (g : G) {x : X} (γ : Path x (g • x)) : Continuous (equivariantPathExtension g γ) := by
  apply pathExtensionInterval_locallyFinite.continuous pathExtensionInterval_cover
    (fun _ => isClosed_Icc)
  intro n
  have hc : Continuous (fun t : ℝ => g^n • γ.extend (t-(n:ℝ))) :=
    (continuous_const_smul (g^n)).comp (γ.continuous_extend.comp (continuous_id.sub continuous_const))
  apply hc.continuousOn.congr
  intro t ht
  exact equivariantPathExtension_on_interval g γ n ht

/-- The genuine curve passes through the actual iterated orbit points at all integers. -/
theorem equivariantPathExtension_int {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (g : G) {x : X} (γ : Path x (g • x)) (n : ℤ) :
    equivariantPathExtension g γ (n:ℝ) = g^n • x := by
  rw [equivariantPathExtension_on_interval g γ n ⟨le_rfl,by linarith⟩,sub_self,Path.extend_zero]

/-- The actual real curve extends the entire given path, with its original parametrization. -/
theorem equivariantPathExtension_unitInterval {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (g : G) {x : X} (γ : Path x (g • x)) (t : I) :
    equivariantPathExtension g γ t = γ t := by
  rw [equivariantPathExtension_on_interval g γ 0 (by
      simpa only [pathExtensionInterval,Int.cast_zero,zero_add] using t.property),
    zpow_zero,one_smul,Int.cast_zero,sub_zero,Path.extend_extends']

/-- The genuine global curve is equivariant under unit translation of its real parameter. -/
theorem equivariantPathExtension_add_one {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (g : G) {x : X} (γ : Path x (g • x)) (t : ℝ) :
    equivariantPathExtension g γ (t+1) = g • equivariantPathExtension g γ t := by
  let n := ⌊t⌋
  have ht : t ∈ pathExtensionInterval n := ⟨Int.floor_le t,(Int.lt_floor_add_one t).le⟩
  have ht' : t+1 ∈ pathExtensionInterval (n+1) := by
    change ((n+1:ℤ):ℝ) ≤ t+1 ∧ t+1 ≤ ((n+1:ℤ):ℝ)+1
    push_cast
    constructor <;> linarith [ht.1,ht.2]
  rw [equivariantPathExtension_on_interval g γ (n+1) ht',equivariantPathExtension_on_interval g γ n ht]
  have harg : t+1-((n+1:ℤ):ℝ) = t-(n:ℝ) := by push_cast; ring
  have hpow : g^(n+1) = g*g^n := by rw [add_comm n 1,zpow_add,zpow_one]
  rw [harg,hpow,mul_smul]

/-- The full image is exactly all integer iterates of the genuine compact original path. -/
theorem equivariantPathExtension_range {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (g : G) {x : X} (γ : Path x (g • x)) :
    range (equivariantPathExtension g γ) = ⋃ n : ℤ, g^n • range γ := by
  apply subset_antisymm
  · rintro y ⟨t,rfl⟩
    let n := ⌊t⌋
    have ht : t ∈ pathExtensionInterval n := ⟨Int.floor_le t,(Int.lt_floor_add_one t).le⟩
    rw [equivariantPathExtension_on_interval g γ n ht]
    have hm : γ.extend (t-(n:ℝ)) ∈ range γ := by
      rw [←γ.extend_range]
      exact mem_range_self _
    exact mem_iUnion.mpr ⟨n,smul_mem_smul_set hm⟩
  · intro y hy
    obtain ⟨n,z,⟨u,rfl⟩,hn⟩ := mem_iUnion.mp hy
    refine ⟨(n:ℝ)+(u:ℝ),?_⟩
    have ht : (n:ℝ)+(u:ℝ) ∈ pathExtensionInterval n := by
      change (n:ℝ) ≤ (n:ℝ)+(u:ℝ) ∧ (n:ℝ)+(u:ℝ) ≤ (n:ℝ)+1
      constructor <;> linarith [u.property.1,u.property.2]
    rw [equivariantPathExtension_on_interval g γ n ht,add_sub_cancel_left,Path.extend_extends']
    exact hn

/-- The entire actual real curve stays in any genuine invariant set containing the path. -/
theorem equivariantPathExtension_range_subset {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (g : G) {x : X} (γ : Path x (g • x)) (S : Set X)
    (hS : ∀ n : ℤ, ∀ y ∈ S, g^n • y ∈ S) (hγ : range γ ⊆ S) :
    range (equivariantPathExtension g γ) ⊆ S := by
  rw [equivariantPathExtension_range]
  intro y hy
  obtain ⟨n,z,hz,rfl⟩ := mem_iUnion.mp hy
  exact hS n z (hγ hz)

end LowDimensionalTopology.Geometry.DiscreteGroups.Action
