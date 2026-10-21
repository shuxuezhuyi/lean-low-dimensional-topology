module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusDiscontinuity
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.TypeOneGroups
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteCyclicGroups
public import Mathlib.RingTheory.IntegralDomain
@[expose] public section
noncomputable section
open scoped Topology OnePoint
open Set Filter
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius

/-- A finite actual Mobius subgroup fixing infinity has injective multiplier, since a nontrivial translation cannot have finite order. -/
theorem finiteMobius_multiplier_injective (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (hi : H ≤ Mobius.mobiusInftyStabilizer) : Function.Injective (Mobius.subgroupMultiplierHom H hi) := by
  apply (Mobius.subgroupMultiplierHom H hi).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro g hg
  have hm : Mobius.mobiusMultiplier (⟨g.val, hi g.property⟩ : Mobius.mobiusInftyStabilizer) = 1 := hg
  rcases (mobiusMultiplier_eq_one_iff_parabolic_or_identity _).mp hm with hp | he
  · by_cases hn : g.val = 1
    · exact Subtype.ext hn
    have hE := finite_H3_orbit_all_elliptic H Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
      (show (MulAction.orbit H Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).Finite from Set.finite_range (fun f
        : H => f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ))
      g.val g.property hn
    exact False.elim (hE.not_parabolic hp)
  · exact Subtype.ext he

/-- A finite actual Mobius group with a common boundary point is cyclic. -/
theorem finiteMobius_fix_infty_isCyclic (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (hi : H ≤ Mobius.mobiusInftyStabilizer) : IsCyclic H :=
  isCyclic_of_injective_ringHom ((Units.coeHom ℂ).comp (Mobius.subgroupMultiplierHom H hi))
    (Units.val_injective.comp (finiteMobius_multiplier_injective H hi))

/-- The finite-point version is transported by an actual Mobius chart, including a fixed point initially at infinity. -/
theorem finiteMobius_fix_boundary_isCyclic (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : Mobius.ExtendedComplex) (hz : ∀ f ∈ H, f.val z = z) : IsCyclic H := by
  obtain ⟨q, hq⟩ := mobius_exists_send_to_infty z
  let K := DiscreteGroups.Action.Actions.subgroupConjugate q H
  let e : H ≃* K := DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  let : Finite K := Finite.of_surjective e e.surjective
  have hi : K ≤ Mobius.mobiusInftyStabilizer := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H f).mp hf
    change (q * g * q⁻¹).val ∞ = ∞
    rw [← hq]
    change q.val (g.val (q.val.symm (q.val z))) = q.val z
    rw [q.val.symm_apply_apply, hz g hg]
  let : IsCyclic K := finiteMobius_fix_infty_isCyclic K hi
  exact isCyclic_of_injective e.toMonoidHom e.injective

/-- For a properly discontinuous isometric action, a genuine metric ball is preserved exactly by the centre stabilizer and separated from every other translate. -/
theorem properlyDiscontinuous_isometric_ball {G X : Type*} [Group G] [MetricSpace X]
    [LocallyCompactSpace X] [MulAction G X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X] (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X) :
    ∃ r : ℝ, 0 < r ∧ ∀ g : G,
      (g • x = x → (fun y : X => g • y) '' Metric.ball x r = Metric.ball x r) ∧
      (g • x ≠ x → Disjoint ((fun y : X => g • y) '' Metric.ball x r) (Metric.ball x r)) := by
  obtain ⟨U, hU, hsep⟩ := ProperlyDiscontinuousSMul.exists_nhds_disjoint_image G x
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨r, hr, ?_⟩
  intro g
  constructor
  · intro hg
    let E : X ≃ᵢ X := { toEquiv := MulAction.toPerm g, isometry_toFun := hi g }
    calc
      _ = E '' Metric.ball x r := rfl
      _ = Metric.ball (E x) r := E.image_ball x r
      _ = Metric.ball x r := by change Metric.ball (g • x) r = _; rw [hg]
  · intro hg
    exact (hsep g hg).mono (Set.image_mono hrU) hrU

/-- With the original H3 path distance and actual Mobius action. -/
theorem mobius_hyperbolic_separating_ball (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    ∃ r : ℝ, 0 < r ∧ ∀ g : H,
      (g • x = x → (fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => g • p) '' {p |
        Mobius.upperHalfSpacePathDist p x < r} =
        {p | Mobius.upperHalfSpacePathDist p x < r}) ∧
      (g • x ≠ x → Disjoint ((fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => g • p) '' {p |
        Mobius.upperHalfSpacePathDist p x < r})
        {p | Mobius.upperHalfSpacePathDist p x < r}) := by
  let proper : ProperlyDiscontinuousSMul H Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
    (DiscreteGroups.Action.isDiscontinuous_iff_properlyDiscontinuousSMul H
      Hyperbolic.QuaternionHalfSpace.UpperHalfSpace).mp
      (discreteMobius_isDiscontinuous_H3 H hH)
  let compact : LocallyCompactSpace Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
    Hyperbolic.QuaternionHalfSpace.isOpen_upperHalfSpaceSet.locallyCompactSpace
  let cont : ContinuousConstSMul H Hyperbolic.QuaternionHalfSpace.UpperHalfSpace := ⟨fun g =>
    (Mobius.mobiusPoincareHomeomorph g.val).continuous⟩
  have hi (g : H) := @Isometry.of_dist_eq Hyperbolic.QuaternionHalfSpace.UpperHalfSpace
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace
    upperHalfSpaceHyperbolicMetricSpace.toPseudoMetricSpace
    upperHalfSpaceHyperbolicMetricSpace.toPseudoMetricSpace
    (fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => g • p) (Mobius.upperHalfSpacePathDist_smul g.val)
  obtain ⟨r, hr, hballs⟩ := @properlyDiscontinuous_isometric_ball H Hyperbolic.QuaternionHalfSpace.UpperHalfSpace
    inferInstance upperHalfSpaceHyperbolicMetricSpace compact inferInstance cont proper hi x
  refine ⟨r, hr, ?_⟩
  intro g
  exact hballs g


/-- The genuine local-neighbourhood form allows finite stabilizers and preserves the whole centre stabilizer exactly. -/
theorem properlyDiscontinuous_invariant_neighbourhood {G X : Type*} [Group G] [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [MulAction G X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X] (x : X) :
    ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ ∀ g : G,
      (g • x = x → (fun y : X => g • y) '' N = N) ∧
      (g • x ≠ x → Disjoint ((fun y : X => g • y) '' N) N) := by
  obtain ⟨U, hU, hsep⟩ := ProperlyDiscontinuousSMul.exists_nhds_disjoint_image G x
  let S := MulAction.stabilizer G x
  let : Finite S := (ProperlyDiscontinuousSMul.finite_stabilizer (Γ := G) x).to_subtype
  let N : Set X := ⋂ s : S, (fun y : X => s.val • y) ⁻¹' interior U
  have hNopen : IsOpen N := isOpen_iInter_of_finite fun s =>
    isOpen_interior.preimage (continuous_const_smul s.val)
  have hxU : x ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  have hxN : x ∈ N := by
    change x ∈ ⋂ s : S, (fun y : X => s.val • y) ⁻¹' interior U
    simp only [Set.mem_iInter, Set.mem_preimage]
    intro s
    rw [MulAction.mem_stabilizer_iff.mp s.property]
    exact hxU
  have hNU : N ⊆ U := by
    intro y hy
    have h := (Set.mem_iInter.mp hy) (1 : S)
    change (1 : G) • y ∈ interior U at h
    rw [one_smul] at h
    exact interior_subset h
  have hmap (g : G) (hg : g • x = x) (y : X) (hy : y ∈ N) : g • y ∈ N := by
    let a : S := ⟨g, hg⟩
    change g • y ∈ ⋂ s : S, (fun y : X => s.val • y) ⁻¹' interior U
    simp only [Set.mem_iInter, Set.mem_preimage]
    intro s
    have hh := (Set.mem_iInter.mp hy) (s * a)
    change (s.val * g) • y ∈ interior U at hh
    simpa only [mul_smul] using hh
  refine ⟨N, hNopen, hxN, ?_⟩
  intro g
  constructor
  · intro hg
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hmap g hg z hz
    · intro hy
      have hgi : g⁻¹ • x = x := by rw [inv_smul_eq_iff]; exact hg.symm
      exact ⟨g⁻¹ • y, hmap g⁻¹ hgi y hy, smul_inv_smul g y⟩
  · intro hg
    exact (hsep g hg).mono (Set.image_mono hNU) hNU


open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius

/-- An actual affine Mobius map fixing an H3 point fixes the finite boundary point given by its horizontal coordinate. -/
theorem mobius_fix_infty_H3_horizontal (f : Mobius.complexMobiusGroup) (hi : f.val ∞ = ∞)
    (p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (hp : f • p = p) :
    f.val ((Hyperbolic.QuaternionHalfSpace.quaternionHorizontal p.val : ℂ) : Mobius.ExtendedComplex) =
      (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal p.val : ℂ) := by
  let fi : Mobius.mobiusInftyStabilizer := ⟨f, hi⟩
  have hfaff : f = Mobius.affineMobius (Mobius.mobiusMultiplier fi) (Mobius.mobiusAffineConstant fi)
    (Mobius.mobiusMultiplier fi).ne_zero :=
    Mobius.mobius_affine_representation fi
  have hh := congrArg (fun q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
    Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val) hp
  rw [hfaff, Mobius.affineMobius_smul, Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint] at hh
  change (fi.val : Equiv.Perm Mobius.ExtendedComplex) (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal p.val :
    ℂ) = (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal p.val : ℂ)
  rw [Mobius.mobius_affine_formula fi, hh]

/-- A finite actual Mobius subgroup with a common boundary point has a distinct second boundary point fixed by the entire subgroup. -/
theorem finiteMobius_common_fixed_second_point (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : Mobius.ExtendedComplex) (hfix : ∀ f ∈ H, f.val z = z) :
    ∃ w : Mobius.ExtendedComplex, w ≠ z ∧ ∀ f ∈ H, f.val w = w := by
  obtain ⟨q, hq⟩ := Mobius.mobius_exists_send_to_infty z
  let K := DiscreteGroups.Action.Actions.subgroupConjugate q H
  let e : H ≃* K := DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  let : Finite K := Finite.of_surjective e e.surjective
  have hi : K ≤ Mobius.mobiusInftyStabilizer := mobius_subgroupConjugate_le_inftyStabilizer H z
    (fun f => hfix f f.property) q hq
  obtain ⟨p, hp⟩ := Mobius.mobius_finite_subgroup_common_H3_fixed K
  let c : Mobius.ExtendedComplex := (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal p.val : ℂ)
  have hc : c ≠ ∞ := OnePoint.coe_ne_infty _
  have hcfixed : ∀ f ∈ K, f.val c = c := by
    intro f hf
    exact mobius_fix_infty_H3_horizontal f (hi hf) p (hp f hf)
  let w := q.val.symm c
  have hw : q.val w = c := q.val.apply_symm_apply c
  refine ⟨w, ?_, ?_⟩
  · intro hwz
    apply hc
    rw [← hw, hwz, hq]
  · intro f hf
    have hconj := hcfixed (q * f * q⁻¹) ((DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨f,
      hf, rfl⟩)
    exact (Mobius.mobius_conjugate_boundary_fixed_iff f q c).mp hconj

/-- For any chosen endpoint-normalizing conjugator, a finite subgroup fixing both endpoints is cyclic and consists entirely of genuine unit rotations. -/
theorem finiteMobius_pair_normalization_rotations (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z w : Mobius.ExtendedComplex) (hfix : ∀ f ∈ H, f.val z = z ∧ f.val w = w)
    (q : Mobius.complexMobiusGroup) (hqz : q.val z = (0 : ℂ)) (hqw : q.val w = ∞) :
    Finite (DiscreteGroups.Action.Actions.subgroupConjugate q H) ∧ IsCyclic
      (DiscreteGroups.Action.Actions.subgroupConjugate q H) ∧
      ∀ f ∈ DiscreteGroups.Action.Actions.subgroupConjugate q H, ∃ a : ℂˣ, ‖(a : ℂ)‖ = 1 ∧ f =
        Mobius.mobiusScaling a := by
  let K := DiscreteGroups.Action.Actions.subgroupConjugate q H
  let e : H ≃* K := DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  let : Finite K := Finite.of_surjective e e.surjective
  have hk (f : Mobius.complexMobiusGroup) (hf : f ∈ K) : f.val (0 : ℂ) = (0 : ℂ) ∧ f.val ∞ = ∞ := by
    obtain ⟨g, hg, rfl⟩ := (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H f).mp hf
    have hgz := mobius_conjugate_fixedpoint g q z (hfix g hg).1
    have hgw := mobius_conjugate_fixedpoint g q w (hfix g hg).2
    rw [hqz] at hgz
    rw [hqw] at hgw
    exact ⟨hgz, hgw⟩
  have hi : K ≤ Mobius.mobiusInftyStabilizer := fun f hf => (hk f hf).2
  have hz : ∀ f ∈ K, f.val (0 : ℂ) = (0 : ℂ) := fun f hf => (hk f hf).1
  exact ⟨inferInstance, finiteMobius_fix_zero_infty_isCyclic K hi hz,
    fun f hf => finiteMobius_fix_zero_infty_rotation K hi hz ⟨f, hf⟩⟩

/-- The entire finite stabilizer can be normalized at once: its prescribed fixed point goes to zero, a distinct common fixed point goes to infinity, and all transformed elements are unit rotations. -/
theorem finiteMobius_common_fixed_normalization (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : Mobius.ExtendedComplex) (hfix : ∀ f ∈ H, f.val z = z) :
    ∃ w : Mobius.ExtendedComplex, w ≠ z ∧ ∃ q : Mobius.complexMobiusGroup,
      q.val z = (0 : ℂ) ∧ q.val w = ∞ ∧
      Finite (DiscreteGroups.Action.Actions.subgroupConjugate q H) ∧ IsCyclic
        (DiscreteGroups.Action.Actions.subgroupConjugate q H) ∧
      ∀ f ∈ DiscreteGroups.Action.Actions.subgroupConjugate q H, ∃ a : ℂˣ, ‖(a : ℂ)‖ = 1 ∧ f =
        Mobius.mobiusScaling a := by
  obtain ⟨w, hw, hwfix⟩ := finiteMobius_common_fixed_second_point H z hfix
  obtain ⟨q, hqz, hqw⟩ := mobius_exists_send_pair_zero_infty z w (Ne.symm hw)
  exact ⟨w, hw, q, hqz, hqw, finiteMobius_pair_normalization_rotations H z w
    (fun f hf => ⟨hfix f hf, hwfix f hf⟩) q hqz hqw⟩

/-- The actual finite Euclidean disc, considered as a subset of the Riemann sphere. -/
def finiteComplexDisc (r : ℝ) : Set Mobius.ExtendedComplex :=
  ((↑) : ℂ → Mobius.ExtendedComplex) '' Metric.ball (0 : ℂ) r

/-- A round disc obtained by pulling a finite centered disc back by the actual Mobius map. -/
def mobiusNormalizedDisc (q : Mobius.complexMobiusGroup) (r : ℝ) : Set Mobius.ExtendedComplex :=
  q.val.symm '' finiteComplexDisc r

theorem coe_mem_finiteComplexDisc (r : ℝ) (z : ℂ) :
    (z : Mobius.ExtendedComplex) ∈ finiteComplexDisc r ↔ ‖z‖ < r := by
  simp [finiteComplexDisc, Metric.mem_ball, dist_zero_right]

theorem mem_mobiusNormalizedDisc (q : Mobius.complexMobiusGroup) (r : ℝ) (z : Mobius.ExtendedComplex) :
    z ∈ mobiusNormalizedDisc q r ↔ q.val z ∈ finiteComplexDisc r := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hz
    exact ⟨q.val z, hz, q.val.symm_apply_apply z⟩

theorem extendedUnitDisc_isComplexOpenDisc : Mobius.IsComplexOpenDisc Hyperbolic.extendedUnitDisc := by
  refine ⟨Mobius.complexCircle 0 1, Mobius.complexCircle_isGeneralized 0 1 zero_lt_one, (0 : ℂ), ?_, ?_⟩
  · rw [Mobius.unitCircle_compl_eq_disc_union_exterior]
    exact Or.inl (by simp [Hyperbolic.coe_mem_extendedUnitDisc])
  · exact (Mobius.connectedComponentIn_unitCircle_compl_of_mem_disc
      (by simp [Hyperbolic.coe_mem_extendedUnitDisc])).symm

theorem finiteComplexDisc_scaling (a : ℂˣ) :
    (Mobius.mobiusScaling a).val '' Hyperbolic.extendedUnitDisc = finiteComplexDisc ‖(a : ℂ)‖ := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hw
    rw [Mobius.mobiusScaling_coe, coe_mem_finiteComplexDisc, norm_mul]
    exact mul_lt_of_lt_one_right (norm_pos_iff.mpr a.ne_zero) hv
  · rintro ⟨w, hw, rfl⟩
    have hw' : ‖w‖ < ‖(a : ℂ)‖ := by simpa [Metric.mem_ball, dist_zero_right] using hw
    refine ⟨((a⁻¹ : ℂˣ) * w : ℂ), ?_, ?_⟩
    · rw [Hyperbolic.coe_mem_extendedUnitDisc, norm_mul, Units.val_inv_eq_inv_val, norm_inv]
      exact (inv_mul_lt_one₀ (norm_pos_iff.mpr a.ne_zero)).mpr hw'
    · rw [Mobius.mobiusScaling_coe]
      congr 1
      simp

theorem finiteComplexDisc_isComplexOpenDisc {r : ℝ} (hr : 0 < r) :
    Mobius.IsComplexOpenDisc (finiteComplexDisc r) := by
  let a : ℂˣ := Units.mk0 (r : ℂ) (by exact_mod_cast hr.ne')
  have ha : ‖(a : ℂ)‖ = r := by simp [a, Complex.norm_real, abs_of_pos hr]
  rw [← ha, ← finiteComplexDisc_scaling a]
  exact extendedUnitDisc_isComplexOpenDisc.image (Mobius.mobiusScaling a)

theorem mobiusNormalizedDisc_isComplexOpenDisc (q : Mobius.complexMobiusGroup) {r : ℝ} (hr : 0 < r) :
    Mobius.IsComplexOpenDisc (mobiusNormalizedDisc q r) := by
  exact (finiteComplexDisc_isComplexOpenDisc hr).image q⁻¹

theorem mobiusScaling_mapsTo_finiteComplexDisc (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1) (r : ℝ) :
    Set.MapsTo (Mobius.mobiusScaling a).val (finiteComplexDisc r) (finiteComplexDisc r) := by
  rintro z ⟨w, hw, rfl⟩
  rw [Mobius.mobiusScaling_coe, coe_mem_finiteComplexDisc, norm_mul, ha, one_mul]
  simpa [Metric.mem_ball, dist_zero_right] using hw

/-- Conjugating the subgroup to unit rotations makes each pulled-back centered disc invariant. -/
theorem mobiusNormalizedDisc_invariant (H : Subgroup Mobius.complexMobiusGroup) (q : Mobius.complexMobiusGroup)
    (hrot : ∀ f ∈ DiscreteGroups.Action.Actions.subgroupConjugate q H,
      ∃ a : ℂˣ, ‖(a : ℂ)‖ = 1 ∧ f = Mobius.mobiusScaling a) (r : ℝ) :
    ∀ f ∈ H, f.val '' mobiusNormalizedDisc q r = mobiusNormalizedDisc q r := by
  have hm : ∀ f ∈ H, Set.MapsTo f.val (mobiusNormalizedDisc q r) (mobiusNormalizedDisc q r) := by
    intro f hf z hz
    rw [mem_mobiusNormalizedDisc] at hz ⊢
    obtain ⟨a, ha, hfa⟩ := hrot (q * f * q⁻¹)
      ((DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨f, hf, rfl⟩)
    have hx := mobiusScaling_mapsTo_finiteComplexDisc a ha r hz
    rw [← hfa] at hx
    change q.val (f.val (q.val.symm (q.val z))) ∈ finiteComplexDisc r at hx
    simpa only [Equiv.symm_apply_apply] using hx
  intro f hf
  apply Set.Subset.antisymm
  · exact Set.image_subset_iff.mpr (hm f hf)
  · intro z hz
    refine ⟨f.val.symm z, hm f⁻¹ (H.inv_mem hf) hz, f.val.apply_symm_apply z⟩

/-- Centered finite discs pull back to a genuine round-disc neighborhood basis with closure control. -/
theorem mobiusNormalizedDisc_closure_basis (q : Mobius.complexMobiusGroup) (z : Mobius.ExtendedComplex)
    (hqz : q.val z = (0 : ℂ)) (U : Set Mobius.ExtendedComplex) (hU : IsOpen U) (hzU : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Mobius.IsComplexOpenDisc (mobiusNormalizedDisc q r) ∧
      z ∈ mobiusNormalizedDisc q r ∧ closure (mobiusNormalizedDisc q r) ⊆ U := by
  let T : ℂ → Mobius.ExtendedComplex := fun w => q.val.symm (w : Mobius.ExtendedComplex)
  have hT : Continuous T := (Mobius.mobiusBoundaryHomeomorph q).symm.continuous.comp OnePoint.continuous_coe
  have hTzero : T 0 = z := by
    apply q.val.injective
    simpa only [T, Equiv.apply_symm_apply] using hqz.symm
  have hpre : T ⁻¹' U ∈ nhds (0 : ℂ) := (hU.preimage hT).mem_nhds (by simpa [hTzero] using hzU)
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hpre
  have him : mobiusNormalizedDisc q r = T '' Metric.ball (0 : ℂ) r := by
    rw [mobiusNormalizedDisc, finiteComplexDisc, Set.image_image]
  have hclosed : IsClosed (T '' Metric.closedBall (0 : ℂ) r) :=
    ((isCompact_closedBall (0 : ℂ) r).image hT).isClosed
  have hcl : closure (mobiusNormalizedDisc q r) ⊆ T '' Metric.closedBall (0 : ℂ) r := by
    apply closure_minimal _ hclosed
    rw [him]
    exact Set.image_mono Metric.ball_subset_closedBall
  refine ⟨r, hr, mobiusNormalizedDisc_isComplexOpenDisc q hr, ?_, ?_⟩
  · rw [him, ← hTzero]
    exact Set.mem_image_of_mem T (by simpa using hr)
  · exact hcl.trans (Set.image_subset_iff.mpr hsub)

/-- Every finite boundary stabilizer has arbitrarily small invariant genuine round discs,
with the prescribed point as their normalized center and with closure in the given open set. -/
theorem finiteMobius_common_fixed_roundDisc_basis (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : Mobius.ExtendedComplex) (hfix : ∀ f ∈ H, f.val z = z)
    (U : Set Mobius.ExtendedComplex) (hU : IsOpen U) (hzU : z ∈ U) :
    ∃ q : Mobius.complexMobiusGroup, ∃ r : ℝ, 0 < r ∧ q.val z = (0 : ℂ) ∧
      Finite (DiscreteGroups.Action.Actions.subgroupConjugate q H) ∧ IsCyclic
        (DiscreteGroups.Action.Actions.subgroupConjugate q H) ∧
      (∀ f ∈ DiscreteGroups.Action.Actions.subgroupConjugate q H, ∃ a : ℂˣ, ‖(a : ℂ)‖ = 1 ∧ f =
        Mobius.mobiusScaling a) ∧
      Mobius.IsComplexOpenDisc (mobiusNormalizedDisc q r) ∧ z ∈ mobiusNormalizedDisc q r ∧
      closure (mobiusNormalizedDisc q r) ⊆ U ∧
      ∀ f ∈ H, f.val '' mobiusNormalizedDisc q r = mobiusNormalizedDisc q r := by
  obtain ⟨w, _, q, hqz, _, hfin, hcyc, hrot⟩ := finiteMobius_common_fixed_normalization H z hfix
  obtain ⟨r, hr, hdisc, hz, hcl⟩ := mobiusNormalizedDisc_closure_basis q z hqz U hU hzU
  exact ⟨q, r, hr, hqz, hfin, hcyc, hrot, hdisc, hz, hcl,
    mobiusNormalizedDisc_invariant H q hrot r⟩


/-- The prescribed subgroup's boundary stabilizer, regarded as an actual Mobius subgroup. -/
def mobiusBoundaryStabilizer (H : Subgroup Mobius.complexMobiusGroup) (z : Mobius.ExtendedComplex) :
    Subgroup Mobius.complexMobiusGroup := (MulAction.stabilizer H z).map H.subtype

theorem mem_mobiusBoundaryStabilizer (H : Subgroup Mobius.complexMobiusGroup) (z : Mobius.ExtendedComplex)
    (g : Mobius.complexMobiusGroup) : g ∈ mobiusBoundaryStabilizer H z ↔ g ∈ H ∧ g.val z = z := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.property, ha⟩
  · rintro ⟨hg, hz⟩
    exact ⟨⟨g, hg⟩, hz, rfl⟩

theorem mobiusBoundaryStabilizer_finite (H : Subgroup Mobius.complexMobiusGroup)
    {S : Set Mobius.ExtendedComplex} (hD : IsMobiusDiscontinuousOn H S) (z : Mobius.ExtendedComplex)
    (hz : z ∈ S) : (mobiusBoundaryStabilizer H z : Set Mobius.complexMobiusGroup).Finite := by
  exact (hD.finite_stabilizer z hz).image H.subtype

/-- Actual invariant round-disc neighborhoods for a discontinuous action on an open sphere domain,
including finite elliptic stabilizers and points initially at infinity. -/
theorem mobius_discontinuous_roundDisc (H : Subgroup Mobius.complexMobiusGroup)
    (S : Set Mobius.ExtendedComplex) (hS : IsOpen S)
    (hInv : ∀ (g : H) z, z ∈ S → g • z ∈ S)
    (hD : IsMobiusDiscontinuousOn H S) (z : Mobius.ExtendedComplex) (hz : z ∈ S) :
    ∃ q : Mobius.complexMobiusGroup, ∃ r : ℝ, 0 < r ∧ q.val z = (0 : ℂ) ∧
      Mobius.IsComplexOpenDisc (mobiusNormalizedDisc q r) ∧ z ∈ mobiusNormalizedDisc q r ∧
      closure (mobiusNormalizedDisc q r) ⊆ S ∧
      (∀ f ∈ DiscreteGroups.Action.Actions.subgroupConjugate q (mobiusBoundaryStabilizer H z),
        ∃ a : ℂˣ, ‖(a : ℂ)‖ = 1 ∧ f = Mobius.mobiusScaling a) ∧
      ∀ g : H,
        (g.val.val z = z → g.val.val '' mobiusNormalizedDisc q r = mobiusNormalizedDisc q r) ∧
        (g.val.val z ≠ z → Disjoint (g.val.val '' mobiusNormalizedDisc q r) (mobiusNormalizedDisc q r)) := by
  let : MulAction H S := DiscreteGroups.Action.invariantSubsetMulAction S hInv
  let : LocallyCompactSpace S := hS.locallyCompactSpace
  let : ContinuousConstSMul H S := ⟨fun g =>
    Continuous.subtype_mk ((Mobius.continuous_mobiusBoundary g.val).comp continuous_subtype_val) _⟩
  let : ProperlyDiscontinuousSMul H S :=
    (DiscreteGroups.Action.isDiscontinuous_iff_properlyDiscontinuousSMul H S).mp
      ((isMobiusDiscontinuousOn_iff_subtype H S hInv).mp hD)
  let x : S := ⟨z, hz⟩
  obtain ⟨N, hNopen, hxN, hN⟩ := properlyDiscontinuous_invariant_neighbourhood (G := H) x
  let U : Set Mobius.ExtendedComplex := Subtype.val '' N
  have hU : IsOpen U := hS.isOpenEmbedding_subtypeVal.isOpenMap N hNopen
  have hzU : z ∈ U := ⟨x, hxN, rfl⟩
  have hUS : U ⊆ S := by rintro _ ⟨w, _, rfl⟩; exact w.property
  have hSep (g : H) (hg : g.val.val z ≠ z) : Disjoint (g.val.val '' U) U := by
    have hneq : g • x ≠ x := fun he => hg (congrArg Subtype.val he)
    apply Set.disjoint_left.mpr
    rintro w ⟨v, ⟨v', hv', rfl⟩, rfl⟩ ⟨w', hw', he⟩
    apply Set.disjoint_left.mp ((hN g).2 hneq) ⟨v', hv', rfl⟩
    have hwe : w' = g • v' := Subtype.ext he
    change g • v' ∈ N
    rwa [← hwe]
  let K := mobiusBoundaryStabilizer H z
  let : Finite K := (mobiusBoundaryStabilizer_finite H hD z hz).to_subtype
  have hK : ∀ f ∈ K, f.val z = z := fun f hf => (mem_mobiusBoundaryStabilizer H z f).mp hf |>.2
  obtain ⟨q, r, hr, hqz, _, _, hrot, hd, hzN, hcl, hPres⟩ :=
    finiteMobius_common_fixed_roundDisc_basis K z hK U hU hzU
  refine ⟨q, r, hr, hqz, hd, hzN, hcl.trans hUS, hrot, ?_⟩
  have hNU : mobiusNormalizedDisc q r ⊆ U := subset_closure.trans hcl
  intro g
  constructor
  · intro hg
    exact hPres g.val ((mem_mobiusBoundaryStabilizer H z g.val).mpr ⟨g.property, hg⟩)
  · intro hg
    exact (hSep g hg).mono (Set.image_mono hNU) hNU

end LowDimensionalTopology.Geometry.DiscreteGroups
