/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.EllipticFixedPointExamples
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteDilationGroups
@[expose] public section
open Set Filter
open scoped Topology OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
noncomputable section

/-- The scaling generator z ↦ 2z of an elementary discrete subgroup. -/
def orbitCounterexampleDilationUnit : ℂˣ := Units.mk0 2 (by norm_num)

def orbitCounterexampleDilation : Mobius.complexMobiusGroup := Mobius.mobiusScaling orbitCounterexampleDilationUnit

def orbitCounterexampleDilationGroup : Subgroup Mobius.complexMobiusGroup :=
  Subgroup.zpowers orbitCounterexampleDilation

theorem orbitCounterexampleDilation_zpow (n : ℤ) :
    orbitCounterexampleDilation ^ n = Mobius.mobiusScaling (orbitCounterexampleDilationUnit ^ n) := by
  change (mobiusScalingHom orbitCounterexampleDilationUnit) ^ n = _
  exact (map_zpow mobiusScalingHom orbitCounterexampleDilationUnit n).symm

theorem orbitCounterexampleDilation_zpow_norm (n : ℤ) (z : ℂ) :
    ‖((orbitCounterexampleDilationUnit ^ n : ℂˣ) : ℂ) * z‖ = (2 : ℝ) ^ n * ‖z‖ := by
  rw [norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow]
  norm_num [orbitCounterexampleDilationUnit]

def orbitCounterexampleAnnulus : Set Mobius.ExtendedComplex :=
  OnePoint.some '' {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < 2}

theorem orbitCounterexampleAnnulus_open : IsOpen orbitCounterexampleAnnulus :=
  OnePoint.isOpenEmbedding_coe.isOpenMap _
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const))

theorem orbitCounterexampleAnnulus_nonempty : orbitCounterexampleAnnulus.Nonempty := by
  refine ⟨((3 / 2 : ℂ) : Mobius.ExtendedComplex), ?_⟩
  exact ⟨(3 / 2 : ℂ), by norm_num, rfl⟩

theorem orbitCounterexampleAnnulus_packing :
    IsMobiusPacking orbitCounterexampleDilationGroup orbitCounterexampleAnnulus := by
  intro g hg
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
  have hn0 : n ≠ 0 := by
    intro h
    apply hg
    apply Subtype.ext
    rw [← hn, h, zpow_zero]
    rfl
  apply Set.disjoint_left.mpr
  rintro w ⟨v, hv, hgv⟩ hw
  obtain ⟨z, ⟨hz1, hz2⟩, rfl⟩ := hv
  rw [← hn, orbitCounterexampleDilation_zpow, Mobius.mobiusScaling_coe] at hgv
  obtain ⟨z', ⟨hz'1, hz'2⟩, he⟩ := hw
  have heq : z' = ((orbitCounterexampleDilationUnit ^ n : ℂˣ) : ℂ) * z :=
    OnePoint.coe_injective (he.trans hgv.symm)
  rw [heq, orbitCounterexampleDilation_zpow_norm] at hz'1 hz'2
  rcases lt_or_gt_of_ne hn0 with hnneg | hnpos
  · have hnle : n ≤ -1 := Int.le_sub_one_of_lt hnneg
    have hpow : (2 : ℝ) ^ n ≤ 1 / 2 := by
      have h := zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hnle
      norm_num at h ⊢
      exact h
    nlinarith [norm_nonneg z]
  · have hnle : (1 : ℤ) ≤ n := Int.add_one_le_iff.mpr hnpos
    have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
      simpa using zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hnle
    nlinarith [norm_nonneg z]

theorem orbitCounterexampleDilationGroup_discrete :
    Mobius.IsDiscreteMobiusSubgroup orbitCounterexampleDilationGroup := by
  apply isMobiusDiscontinuousOn_open_discrete orbitCounterexampleDilationGroup
    (mobiusSaturation orbitCounterexampleDilationGroup orbitCounterexampleAnnulus)
    (mobiusSaturation_isOpen _ orbitCounterexampleAnnulus_open)
    (orbitCounterexampleAnnulus_nonempty.mono (subset_mobiusSaturation _ _))
  exact mobius_openPacking_saturation_discontinuous _ _ orbitCounterexampleAnnulus_open
    orbitCounterexampleAnnulus_packing

theorem orbitCounterexampleDilationGroup_fixes_zero (g : orbitCounterexampleDilationGroup) :
    g • ((0 : ℂ) : Mobius.ExtendedComplex) = ((0 : ℂ) : Mobius.ExtendedComplex) := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
  change g.val.val (0 : ℂ) = (0 : ℂ)
  rw [← hn, orbitCounterexampleDilation_zpow, mobiusScaling_zero]

theorem orbitCounterexampleDilationGroup_elementary :
    IsElementary orbitCounterexampleDilationGroup :=
  isElementary_of_boundary_fixed _ (0 : ℂ) orbitCounterexampleDilationGroup_fixes_zero

/-- An orbit consisting of a fixed point cannot accumulate at any other point. -/
theorem mobiusOrbitLimitSet_subset_singleton_of_fixed (H : Subgroup Mobius.complexMobiusGroup)
    (z : Mobius.ExtendedComplex) (hz : ∀ g : H, g • z = z) :
    mobiusOrbitLimitSet H z ⊆ {z} := by
  rintro w ⟨u, _, hu⟩
  have hc : (fun n => u n • z) = (fun _ : ℕ => z) := funext fun n => hz (u n)
  rw [hc] at hu
  exact (tendsto_nhds_unique hu tendsto_const_nhds : w = z)

theorem orbitCounterexampleDilationGroup_infty_limit :
    ∞ ∈ mobiusLimitSet orbitCounterexampleDilationGroup := by
  apply mobiusLoxodromicFixedPointSet_subset_limitSet
  refine ⟨⟨orbitCounterexampleDilation, Subgroup.mem_zpowers _⟩, ?_, ?_⟩
  · change Mobius.MobiusLoxodromic (Mobius.mobiusScaling orbitCounterexampleDilationUnit)
    rw [mobiusScaling_eq_standard _ (by norm_num [orbitCounterexampleDilationUnit])]
    apply Mobius.mobiusStandardElement_isLoxodromic
    norm_num [orbitCounterexampleDilationUnit]
  · exact Mobius.mobiusScaling_infty _

theorem orbitCounterexampleDilationGroup_orbitLimit_ne :
    mobiusLimitSet orbitCounterexampleDilationGroup ≠
      mobiusOrbitLimitSet orbitCounterexampleDilationGroup (0 : ℂ) := by
  intro he
  have h := mobiusOrbitLimitSet_subset_singleton_of_fixed _ _
    orbitCounterexampleDilationGroup_fixes_zero (he ▸ orbitCounterexampleDilationGroup_infty_limit)
  exact OnePoint.coe_ne_infty (0 : ℂ) h.symm

/-- The full actual Mobius subgroup preserving the open unit disc. -/
def orbitCounterexampleDiscGroup : Subgroup Mobius.complexMobiusGroup :=
  MulAction.stabilizer Mobius.complexMobiusGroup Hyperbolic.extendedUnitDisc

theorem orbitCounterexampleDiscGroup_nonElementary :
    IsNonElementary orbitCounterexampleDiscGroup := by
  obtain ⟨q, hq⟩ := Mobius.standardComplexHalfDisc_isDisc.normalize
  have hle : jorgensenSharpnessGroup.map (MulAut.conj q).toMonoidHom ≤
      orbitCounterexampleDiscGroup := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hf
    exact Mobius.mobius_disc_conjugate_preserves g q hq
      (modularGroup_preserves_halfDisc ⟨g, hg⟩)
  intro he
  exact (jorgensenSharpnessGroup_nonElementary.conjugation q) (he.mono hle)

theorem orbitCounterexampleDiscGroup_zero_ordinary :
    ((0 : ℂ) : Mobius.ExtendedComplex) ∈ mobiusOrdinarySet orbitCounterexampleDiscGroup := by
  apply mobius_proper_invariant_open_subset_ordinary _
    orbitCounterexampleDiscGroup_nonElementary Hyperbolic.extendedUnitDisc
    Mobius.isOpen_extendedUnitDisc ?_ ?_ ((Hyperbolic.coe_mem_extendedUnitDisc 0).mpr (by norm_num))
  · intro he
    have hi : ∞ ∈ Hyperbolic.extendedUnitDisc := he ▸ Set.mem_univ ∞
    exact Mobius.infty_not_mem_extendedUnitDisc hi
  · intro g z hz
    have he : g.val.val '' Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc := g.property
    rw [← he]
    exact ⟨z, hz, rfl⟩

theorem orbitCounterexampleRotation_den_ne_zero (n : ℕ) : (n : ℂ) - Complex.I ≠ 0 := by
  intro he
  have h := congrArg Complex.im he
  norm_num at h

theorem orbitCounterexampleRotation_num_ne_zero (n : ℕ) : (n : ℂ) + Complex.I ≠ 0 := by
  intro he
  have h := congrArg Complex.im he
  norm_num at h

/-- Infinitely many distinct unit complex numbers, with no density or choice postulate. -/
def orbitCounterexampleRotationUnit (n : ℕ) : ℂˣ :=
  Units.mk0 (((n : ℂ) + Complex.I) / ((n : ℂ) - Complex.I))
    (div_ne_zero (orbitCounterexampleRotation_num_ne_zero n) (orbitCounterexampleRotation_den_ne_zero n))

theorem orbitCounterexampleRotationUnit_norm (n : ℕ) :
    ‖(orbitCounterexampleRotationUnit n : ℂ)‖ = 1 := by
  have hc : starRingEnd ℂ ((n : ℂ) - Complex.I) = (n : ℂ) + Complex.I := by simp
  change ‖((n : ℂ) + Complex.I) / ((n : ℂ) - Complex.I)‖ = 1
  rw [norm_div, ← hc, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr
    (orbitCounterexampleRotation_den_ne_zero n))]

theorem orbitCounterexampleRotationUnit_injective :
    Function.Injective orbitCounterexampleRotationUnit := by
  intro m n he
  have hv := congrArg (fun a : ℂˣ => (a : ℂ)) he
  change ((m : ℂ) + Complex.I) / ((m : ℂ) - Complex.I) =
    ((n : ℂ) + Complex.I) / ((n : ℂ) - Complex.I) at hv
  have hm := (div_eq_div_iff (orbitCounterexampleRotation_den_ne_zero m)
    (orbitCounterexampleRotation_den_ne_zero n)).mp hv
  have hi := congrArg Complex.im hm
  simp only [Complex.mul_im, Complex.add_re, Complex.sub_re, Complex.natCast_re,
    Complex.I_re, add_zero, sub_zero, Complex.sub_im, Complex.add_im,
    Complex.natCast_im, Complex.I_im] at hi
  have heq : (m : ℝ) = n := by linarith
  exact_mod_cast heq

/-- Every unit scaling belongs to the full disc-preserving actual group. -/
theorem mobiusScaling_mem_discGroup (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1) :
    Mobius.mobiusScaling a ∈ orbitCounterexampleDiscGroup := by
  change (Mobius.mobiusScaling a).val '' Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc
  apply Set.Subset.antisymm
  · rintro w ⟨z, hz, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hz
    rw [Mobius.mobiusScaling_coe, Hyperbolic.coe_mem_extendedUnitDisc, norm_mul, ha, one_mul]
    exact hz
  · rintro z ⟨z, hz, rfl⟩
    refine ⟨(((a : ℂ)⁻¹ * z : ℂ) : Mobius.ExtendedComplex), ?_, ?_⟩
    · rw [Hyperbolic.coe_mem_extendedUnitDisc, norm_mul, norm_inv, ha, inv_one, one_mul]
      exact hz
    · rw [Mobius.mobiusScaling_coe, ← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]

def orbitCounterexampleDiscSequence (n : ℕ) : orbitCounterexampleDiscGroup :=
  ⟨Mobius.mobiusScaling (orbitCounterexampleRotationUnit n),
    mobiusScaling_mem_discGroup _ (orbitCounterexampleRotationUnit_norm n)⟩

theorem orbitCounterexampleDiscSequence_injective : Function.Injective orbitCounterexampleDiscSequence := by
  intro m n he
  apply orbitCounterexampleRotationUnit_injective
  apply Units.ext
  have hc := congrArg (fun f : orbitCounterexampleDiscGroup => f.val.val (1 : ℂ)) he
  change (Mobius.mobiusScaling (orbitCounterexampleRotationUnit m)).val (1 : ℂ) =
    (Mobius.mobiusScaling (orbitCounterexampleRotationUnit n)).val (1 : ℂ) at hc
  rw [Mobius.mobiusScaling_coe, Mobius.mobiusScaling_coe] at hc
  exact OnePoint.coe_injective (by simpa only [mul_one] using hc)

theorem orbitCounterexampleDiscGroup_zero_orbitLimit :
    ((0 : ℂ) : Mobius.ExtendedComplex) ∈ mobiusOrbitLimitSet orbitCounterexampleDiscGroup (0 : ℂ) := by
  refine ⟨orbitCounterexampleDiscSequence, orbitCounterexampleDiscSequence_injective, ?_⟩
  convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => ((0 : ℂ) : Mobius.ExtendedComplex)) atTop (𝓝 (0 : ℂ))) using 1
  funext n
  exact mobiusScaling_zero _

theorem orbitCounterexampleDiscGroup_orbitLimit_ne :
    mobiusLimitSet orbitCounterexampleDiscGroup ≠
      mobiusOrbitLimitSet orbitCounterexampleDiscGroup (0 : ℂ) := by
  intro he
  exact orbitCounterexampleDiscGroup_zero_ordinary (he ▸ orbitCounterexampleDiscGroup_zero_orbitLimit)

theorem orbitCounterexampleDiscGroup_not_discrete : ¬Mobius.IsDiscreteMobiusSubgroup orbitCounterexampleDiscGroup := by
  intro hd
  exact orbitCounterexampleDiscGroup_orbitLimit_ne
    (limitSet_eq_orbitLimitSet _ orbitCounterexampleDiscGroup_nonElementary hd (0 : ℂ))

/-- Orbit-limit equality can fail when either non-elementarity or discreteness is omitted. -/
theorem mobius_orbit_limit_hypothesis_counterexamples :
    (Mobius.IsDiscreteMobiusSubgroup orbitCounterexampleDilationGroup ∧
      IsElementary orbitCounterexampleDilationGroup ∧
      mobiusLimitSet orbitCounterexampleDilationGroup ≠
        mobiusOrbitLimitSet orbitCounterexampleDilationGroup (0 : ℂ)) ∧
    (IsNonElementary orbitCounterexampleDiscGroup ∧
      ¬Mobius.IsDiscreteMobiusSubgroup orbitCounterexampleDiscGroup ∧
      mobiusLimitSet orbitCounterexampleDiscGroup ≠
        mobiusOrbitLimitSet orbitCounterexampleDiscGroup (0 : ℂ)) :=
  ⟨⟨orbitCounterexampleDilationGroup_discrete, orbitCounterexampleDilationGroup_elementary,
    orbitCounterexampleDilationGroup_orbitLimit_ne⟩,
    ⟨orbitCounterexampleDiscGroup_nonElementary, orbitCounterexampleDiscGroup_not_discrete,
    orbitCounterexampleDiscGroup_orbitLimit_ne⟩⟩

end
end LowDimensionalTopology.Geometry.DiscreteGroups
