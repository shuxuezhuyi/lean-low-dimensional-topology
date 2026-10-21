/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteDihedralGroups
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteMobiusGroups
public import LowDimensionalTopology.Geometry.Mobius.Topology
public import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
@[expose] public section
noncomputable section
open Set
open scoped Topology OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius

/-- The actual multiplier represents a map fixing both endpoints by complex scaling. -/
theorem dilation_multiplier_representation (H : Subgroup Mobius.complexMobiusGroup)
    (hi : H ≤ Mobius.mobiusInftyStabilizer) (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) (f : H) :
    f.val = Mobius.mobiusScaling (Mobius.subgroupMultiplierHom H hi f) := by
  let fi : Mobius.mobiusInftyStabilizer := ⟨f.val, hi f.property⟩
  change f.val = Mobius.mobiusScaling (Mobius.mobiusMultiplier fi)
  rw [Mobius.mobiusScaling, ← mobiusAffineConstant_zero_of_fix_zero fi (hz _ f.property)]
  exact Mobius.mobius_affine_representation fi

/-- The normalized Frobenius square for the genuine map z ↦ a z. -/
theorem mobiusScaling_normalizedNorm_sq (a : ℂˣ) :
    Mobius.mobiusNormalizedNorm (Mobius.mobiusScaling a) ^ 2 = ‖(a : ℂ)‖ + ‖(a : ℂ)‖⁻¹ := by
  rw [Mobius.mobiusScaling, Mobius.mobiusNormalizedNorm_projection, Mobius.matrixNormalizedNorm, div_pow,
    Auxiliary.Algebra.matrixNorm_sq]
  have ha : 0 < ‖(a : ℂ)‖ := norm_pos_iff.mpr a.ne_zero
  simp only [Mobius.Classification.affineMatrix, Mobius.coefficientMatrix_val, Matrix.det_fin_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    norm_zero, norm_one, one_pow, mul_one, mul_zero, sub_zero]
  rw [Real.sq_sqrt ha.le]
  field_simp
  ring

/-- The logarithm of the actual dilation modulus is an additive-valued group homomorphism. -/
def dilationLogModulusHom (H : Subgroup Mobius.complexMobiusGroup)
    (hi : H ≤ Mobius.mobiusInftyStabilizer) : H →* Multiplicative ℝ where
  toFun f := Multiplicative.ofAdd (Real.log ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖)
  map_one' := by simp
  map_mul' f g := by
    change Real.log ‖((Mobius.subgroupMultiplierHom H hi (f * g) : ℂˣ) : ℂ)‖ =
      Real.log ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖ +
      Real.log ‖((Mobius.subgroupMultiplierHom H hi g : ℂˣ) : ℂ)‖
    rw [map_mul, Units.val_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (Units.ne_zero _))
      (norm_ne_zero_iff.mpr (Units.ne_zero _))]

/-- The actual logarithmic dilation moduli form an additive subgroup of the real line. -/
def dilationLogModulusRange (H : Subgroup Mobius.complexMobiusGroup)
    (hi : H ≤ Mobius.mobiusInftyStabilizer) : AddSubgroup ℝ :=
  (dilationLogModulusHom H hi).toAdditiveLeft.range

/-- The elliptic modulus kernel inside the actual subgroup. -/
def dilationRotationKernel (H : Subgroup Mobius.complexMobiusGroup)
    (hi : H ≤ Mobius.mobiusInftyStabilizer) : Subgroup H := (dilationLogModulusHom H hi).ker

/-- Kernel membership means the genuine complex multiplier has unit modulus. -/
theorem dilationRotationKernel_mem_iff (H : Subgroup Mobius.complexMobiusGroup)
    (hi : H ≤ Mobius.mobiusInftyStabilizer) (f : H) :
    f ∈ dilationRotationKernel H hi ↔ ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖ = 1 := by
  change Real.log ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖ = 0 ↔ _
  constructor
  · exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr (Units.ne_zero _))
  · intro he
    rw [he, Real.log_one]

/-- A bound on logarithmic modulus bounds the actual normalized Mobius norm. -/
theorem dilation_normalizedNorm_le (H : Subgroup Mobius.complexMobiusGroup)
    (hi : H ≤ Mobius.mobiusInftyStabilizer) (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ))
    (f : H) (R : ℝ)
    (hR : |Real.log ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖| ≤ R) :
    Mobius.mobiusNormalizedNorm f.val ≤ Real.exp R + 1 := by
  let r := ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖
  have hr : 0 < r := norm_pos_iff.mpr (Units.ne_zero _)
  have hbound : r ≤ Real.exp R := (Real.log_le_iff_le_exp hr).mp (abs_le.mp hR).2
  have hibound : r⁻¹ ≤ Real.exp R := (Real.log_le_iff_le_exp (inv_pos.mpr hr)).mp (by
    rw [Real.log_inv]
    linarith [(abs_le.mp hR).1])
  have he := mobiusScaling_normalizedNorm_sq (Mobius.subgroupMultiplierHom H hi f)
  rw [← dilation_multiplier_representation H hi hz f] at he
  have hs : Mobius.mobiusNormalizedNorm f.val ^ 2 ≤ (Real.exp R + 1) ^ 2 := by
    change Mobius.mobiusNormalizedNorm f.val ^ 2 = r + r⁻¹ at he
    nlinarith [sq_nonneg (Real.exp R)]
  exact (sq_le_sq₀ (mobiusNormalizedNorm_nonneg _) (by positivity)).mp hs

/-- A discrete actual dilation subgroup has only finitely many elements in every logarithmic shell. -/
theorem dilation_log_shell_finite (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) (R : ℝ) :
    {f : H | |Real.log ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖| ≤ R}.Finite := by
  apply (Mobius.discreteMobius_norm_sublevel_finite H hH (Real.exp R + 1)).subset
  intro f hf
  exact dilation_normalizedNorm_le H hi hz f R hf

/-- The real logarithmic-modulus image has finite intersections with bounded intervals. -/
theorem dilationLogModulusRange_shell_finite (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) (R : ℝ) :
    {t : ℝ | t ∈ dilationLogModulusRange H hi ∧ |t| ≤ R}.Finite := by
  apply ((dilation_log_shell_finite H hH hi hz R).image
    (fun f : H => Real.log ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖)).subset
  rintro t ⟨ht, htR⟩
  obtain ⟨f, hf⟩ := ht
  refine ⟨Additive.toMul f, ?_, ?_⟩
  · change |Real.log ‖((Mobius.subgroupMultiplierHom H hi (Additive.toMul f) : ℂˣ) : ℂ)‖| ≤ R
    change Real.log ‖((Mobius.subgroupMultiplierHom H hi (Additive.toMul f) : ℂˣ) : ℂ)‖ = t at hf
    rw [hf]
    exact htR
  · exact hf

/-- The logarithmic modulus image is discrete, with its genuine subspace topology. -/
theorem dilationLogModulusRange_discrete (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) :
    DiscreteTopology (dilationLogModulusRange H hi) := by
  let A := dilationLogModulusRange H hi
  have hfinite : {t : A | |(t : ℝ)| < 1}.Finite := by
    apply (Set.Finite.preimage Subtype.val_injective.injOn
      (dilationLogModulusRange_shell_finite H hH hi hz 1)).subset
    intro t ht
    exact ⟨t.property, ht.le⟩
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  apply isOpen_singleton_of_finite_mem_nhds (0 : A) ?_ hfinite
  exact (isOpen_lt continuous_subtype_val.abs continuous_const).mem_nhds (by simp)

/-- Discrete actual dilation groups have cyclic logarithmic modulus image. -/
theorem dilationLogModulusRange_isAddCyclic (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) :
    IsAddCyclic (dilationLogModulusRange H hi) :=
  AddSubgroup.isAddCyclic_iff_discreteTopology.mpr (dilationLogModulusRange_discrete H hH hi hz)

/-- The elliptic modulus kernel is finite. -/
theorem dilationRotationKernel_finite (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) : Finite (dilationRotationKernel H hi) := by
  have hs : {f : H | |Real.log ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖| ≤ 0}.Finite :=
    dilation_log_shell_finite H hH hi hz 0
  have he : (dilationRotationKernel H hi : Set H) ⊆
      {f : H | |Real.log ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖| ≤ 0} := by
    intro f hf
    have hf' : Real.log ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖ = 0 := hf
    simp only [mem_ofPred_eq, hf', abs_zero, le_refl]
  exact (hs.subset he).to_subtype

/-- Its multiplier embedding makes the finite elliptic kernel cyclic. -/
theorem dilationRotationKernel_isCyclic (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) : IsCyclic (dilationRotationKernel H hi) := by
  let rotationKernelFinite : Finite (dilationRotationKernel H hi) :=
    dilationRotationKernel_finite H hH hi hz
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom ℂ).comp ((Mobius.subgroupMultiplierHom H hi).comp (dilationRotationKernel H hi).subtype))
    (Units.val_injective.comp
      ((subgroupMultiplierHom_injective_of_fix_zero H hi hz).comp Subtype.val_injective))

/-- The exact cyclic logarithmic image is generated by the modulus of an actual group element. -/
theorem dilationLogModulusRange_generator (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) :
    ∃ g : H, ∀ f : H, ∃ n : ℤ,
      Real.log ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖ =
        n * Real.log ‖((Mobius.subgroupMultiplierHom H hi g : ℂˣ) : ℂ)‖ := by
  obtain ⟨r, hr⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top
    (dilationLogModulusRange H hi)).mp (dilationLogModulusRange_isAddCyclic H hH hi hz)
  have hrmem : r ∈ dilationLogModulusRange H hi := by
    rw [← hr]
    exact AddSubgroup.mem_zmultiples r
  obtain ⟨g, hg⟩ := hrmem
  refine ⟨Additive.toMul g, ?_⟩
  intro f
  have hfmem : Real.log ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖ ∈
      AddSubgroup.zmultiples r := by
    rw [hr]
    exact ⟨Additive.ofMul f, rfl⟩
  obtain ⟨n, hn⟩ := hfmem
  refine ⟨n, ?_⟩
  change Real.log ‖((Mobius.subgroupMultiplierHom H hi (Additive.toMul g) : ℂˣ) : ℂ)‖ = r at hg
  rw [hg, ← hn]
  change n • r = (n : ℝ) * r
  simp only [zsmul_eq_mul]

/-- Every actual dilation is a kernel element times a power of one actual dilation. -/
theorem dilation_rotation_coset_decomposition (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) :
    ∃ g : H, ∀ f : H, ∃ e : dilationRotationKernel H hi, ∃ n : ℤ,
      f = e.val * g ^ n := by
  obtain ⟨g, hg⟩ := dilationLogModulusRange_generator H hH hi hz
  refine ⟨g, ?_⟩
  intro f
  obtain ⟨n, hn⟩ := hg f
  have he : f * (g ^ n)⁻¹ ∈ dilationRotationKernel H hi := by
    change (dilationLogModulusHom H hi) (f * (g ^ n)⁻¹) = 1
    rw [map_mul, map_inv, map_zpow]
    change Real.log ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖ -
      n • Real.log ‖((Mobius.subgroupMultiplierHom H hi g : ℂˣ) : ℂ)‖ = 0
    rw [hn, zsmul_eq_mul, sub_self]
  refine ⟨⟨f * (g ^ n)⁻¹, he⟩, n, ?_⟩
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- Complex scalings form a homomorphism into the actual Mobius group. -/
def mobiusScalingHom : ℂˣ →* Mobius.complexMobiusGroup where
  toFun := Mobius.mobiusScaling
  map_one' := mobiusScaling_one
  map_mul' := mobiusScaling_mul

/-- A generator of the finite rotation kernel gives bounded nonnegative powers. -/
theorem dilationRotationKernel_bounded_generator (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) :
    ∃ w : dilationRotationKernel H hi, ∃ q : ℕ, 0 < q ∧ w ^ q = 1 ∧
      ∀ e : dilationRotationKernel H hi, ∃ k : Fin q, w ^ (k : ℕ) = e := by
  let rotationKernelFinite : Finite (dilationRotationKernel H hi) :=
    dilationRotationKernel_finite H hH hi hz
  let rotationKernelCyclic : IsCyclic (dilationRotationKernel H hi) :=
    dilationRotationKernel_isCyclic H hH hi hz
  obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := dilationRotationKernel H hi)
  refine ⟨w, orderOf w, orderOf_pos w, pow_orderOf_eq_one w, ?_⟩
  intro e
  obtain ⟨m, hm⟩ := (isOfFinOrder_of_finite w).mem_powers_iff_mem_zpowers.mpr (hw e)
  exact ⟨⟨m % orderOf w, Nat.mod_lt _ (orderOf_pos w)⟩, (pow_mod_orderOf w m).trans hm⟩

/-- The exact rotation-times-dilation normal form, with bounded rotation exponent. -/
theorem discreteDilation_normal_form (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) :
    ∃ w g : H, ∃ q : ℕ, 0 < q ∧
      ‖((Mobius.subgroupMultiplierHom H hi w : ℂˣ) : ℂ)‖ = 1 ∧ w ^ q = 1 ∧
        ∀ f : H, ∃ k : Fin q, ∃ n : ℤ, f = w ^ (k : ℕ) * g ^ n := by
  obtain ⟨g, hg⟩ := dilation_rotation_coset_decomposition H hH hi hz
  obtain ⟨w, q, hq, hwq, hw⟩ := dilationRotationKernel_bounded_generator H hH hi hz
  refine ⟨w.val, g, q, hq, (dilationRotationKernel_mem_iff H hi w.val).mp w.property,
    congrArg Subtype.val hwq, ?_⟩
  intro f
  obtain ⟨e, n, he⟩ := hg f
  obtain ⟨k, hk⟩ := hw e
  refine ⟨k, n, ?_⟩
  rw [he, ← hk]
  rfl

/-- The normal form is an exact equality of actual transformation sets. -/
theorem discreteDilation_scaling_normal_form (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) :
    ∃ w a : ℂˣ, ∃ q : ℕ, 0 < q ∧ ‖(w : ℂ)‖ = 1 ∧ w ^ q = 1 ∧
      ∀ f : Mobius.complexMobiusGroup, f ∈ H ↔
        ∃ k : Fin q, ∃ n : ℤ, f = Mobius.mobiusScaling (w ^ (k : ℕ) * a ^ n) := by
  obtain ⟨w, g, q, hq, hwn, hwq, hall⟩ := discreteDilation_normal_form H hH hi hz
  let ω := Mobius.subgroupMultiplierHom H hi w
  let a := Mobius.subgroupMultiplierHom H hi g
  refine ⟨ω, a, q, hq, hwn, ?_, ?_⟩
  · change (Mobius.subgroupMultiplierHom H hi w) ^ q = 1
    rw [← map_pow, hwq, map_one]
  · intro f
    constructor
    · intro hf
      obtain ⟨k, n, he⟩ := hall ⟨f, hf⟩
      refine ⟨k, n, ?_⟩
      have hm := congrArg (Mobius.subgroupMultiplierHom H hi) he
      simp only [map_mul, map_pow, map_zpow] at hm
      calc
        f = Mobius.mobiusScaling (Mobius.subgroupMultiplierHom H hi ⟨f, hf⟩) :=
          dilation_multiplier_representation H hi hz ⟨f, hf⟩
        _ = Mobius.mobiusScaling (ω ^ (k : ℕ) * a ^ n) := congrArg Mobius.mobiusScaling hm
    · rintro ⟨k, n, rfl⟩
      have hw : Mobius.mobiusScaling ω = w.val := (dilation_multiplier_representation H hi hz w).symm
      have hg : Mobius.mobiusScaling a = g.val := (dilation_multiplier_representation H hi hz g).symm
      change mobiusScalingHom (ω ^ (k : ℕ) * a ^ n) ∈ H
      rw [map_mul, map_pow, map_zpow]
      change Mobius.mobiusScaling ω ^ (k : ℕ) * Mobius.mobiusScaling a ^ n ∈ H
      rw [hw, hg]
      exact H.mul_mem (H.pow_mem w.property _) (H.zpow_mem g.property _)

/-- The actual dilation modulus homomorphism has positive real-unit values. -/
def dilationModulusHom (H : Subgroup Mobius.complexMobiusGroup)
    (hi : H ≤ Mobius.mobiusInftyStabilizer) : H →* ℝˣ where
  toFun f := Units.mk0 ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖
    (norm_ne_zero_iff.mpr (Units.ne_zero _))
  map_one' := by apply Units.ext; simp
  map_mul' f g := by apply Units.ext; simp

/-- The modulus image consists of exactly the integer powers of one positive actual modulus. -/
theorem dilationModulusHom_range_powers (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) :
    ∃ g : H, ∀ r : ℝ,
      (∃ f : H, ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖ = r) ↔
        ∃ n : ℤ, r = ‖((Mobius.subgroupMultiplierHom H hi g : ℂˣ) : ℂ)‖ ^ n := by
  obtain ⟨g, hg⟩ := dilationLogModulusRange_generator H hH hi hz
  refine ⟨g, ?_⟩
  intro r
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨n, hn⟩ := hg f
    refine ⟨n, Real.log_injOn_pos (norm_pos_iff.mpr (Units.ne_zero _))
      (zpow_pos (norm_pos_iff.mpr (Units.ne_zero _)) n) ?_⟩
    rw [Real.log_zpow]
    exact hn
  · rintro ⟨n, rfl⟩
    refine ⟨g ^ n, ?_⟩
    rw [map_zpow, Units.val_zpow_eq_zpow_val, norm_zpow]

/-- Away from the translation parameter the standard map is exactly complex scaling. -/
theorem mobiusScaling_eq_standard (a : ℂˣ) (ha : (a : ℂ) ≠ 1) :
    Mobius.mobiusScaling a = Mobius.mobiusStandardElement a := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  induction z using OnePoint.rec with
  | infty => rw [Mobius.mobiusScaling_infty, Mobius.mobiusStandardElement_infty]
  | coe z => rw [Mobius.mobiusScaling_coe, Mobius.mobiusStandardElement_coe, ite_eq_right ha]

/-- A dilation with nonunit modulus is genuinely loxodromic in full three-space. -/
theorem dilation_loxodromic_of_modulus_ne_one (H : Subgroup Mobius.complexMobiusGroup)
    (hi : H ≤ Mobius.mobiusInftyStabilizer) (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ))
    (f : H) (hf : ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖ ≠ 1) :
    Mobius.MobiusLoxodromic f.val := by
  rw [dilation_multiplier_representation H hi hz f,
    mobiusScaling_eq_standard _ (fun he => hf (by rw [he, norm_one]))]
  exact Mobius.mobiusStandardElement_isLoxodromic _ hf

/-- The modulus kernel consists of identity and all genuine elliptic elements. -/
theorem dilationRotationKernel_mem_iff_one_or_elliptic (H : Subgroup Mobius.complexMobiusGroup)
    (hi : H ≤ Mobius.mobiusInftyStabilizer) (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) (f : H) :
    f ∈ dilationRotationKernel H hi ↔ f.val = 1 ∨ Mobius.MobiusElliptic f.val := by
  rw [dilationRotationKernel_mem_iff]
  constructor
  · intro hn
    by_cases hf : f.val = 1
    · exact Or.inl hf
    · right
      have ha : ((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ) ≠ 1 := by
        intro he
        apply hf
        have heu : Mobius.subgroupMultiplierHom H hi f = 1 := Units.ext he
        rw [dilation_multiplier_representation H hi hz f, heu, mobiusScaling_one]
      rw [dilation_multiplier_representation H hi hz f, mobiusScaling_eq_standard _ ha]
      exact Mobius.mobiusStandardElement_isElliptic _ ha hn
  · rintro (he | he)
    · have hf : f = 1 := Subtype.ext he
      rw [hf, map_one, Units.val_one, norm_one]
    · by_contra hn
      exact (dilation_loxodromic_of_modulus_ne_one H hi hz f hn).not_elliptic he

/-- A dilation subgroup has no genuine parabolic element. -/
theorem dilation_no_parabolic (H : Subgroup Mobius.complexMobiusGroup)
    (hi : H ≤ Mobius.mobiusInftyStabilizer) (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ))
    (f : H) : ¬Mobius.MobiusParabolic f.val := by
  rintro ⟨_, a, ha⟩
  have hzero : ((0 : ℂ) : Mobius.ExtendedComplex) = a := (ha _).mp (hz _ f.property)
  have hinfty : (∞ : Mobius.ExtendedComplex) = a := (ha _).mp (hi f.property)
  exact (OnePoint.coe_ne_infty (0 : ℂ)) (hzero.trans hinfty.symm)

/-- The finite cyclic degeneration occurs precisely when every multiplier has modulus one. -/
theorem discreteDilation_finite_iff_unit_moduli (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) :
    Finite H ↔ ∀ f : H, ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖ = 1 := by
  constructor
  · intro hfinite
    let dilationFinite : Finite H := hfinite
    exact finiteMobius_multiplier_unit_norm H hi
  · intro hall
    have hs := dilation_log_shell_finite H hH hi hz 0
    have he : {f : H | |Real.log ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖| ≤ 0} = univ := by
      ext f
      simp only [mem_ofPred_eq, hall f, Real.log_one, abs_zero, le_refl, mem_univ]
    rw [he] at hs
    exact finite_univ_iff.mp hs

/-- The trivial-modulus degeneration is a finite cyclic group of genuine rotations. -/
theorem discreteDilation_unit_moduli_finite_cyclic (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ))
    (hall : ∀ f : H, ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖ = 1) :
    Finite H ∧ IsCyclic H := by
  let dilationFinite : Finite H := (discreteDilation_finite_iff_unit_moduli H hH hi hz).mpr hall
  exact ⟨dilationFinite, finiteMobius_fix_zero_infty_isCyclic H hi hz⟩

/-- Endpoint exchange makes the pointwise endpoint stabilizer have index two, without finiteness assumptions. -/
theorem mobiusEndpointKernel_index_two (H : Subgroup Mobius.complexMobiusGroup)
    (hp : H ≤ mobiusZeroInftyPairStabilizer) (s : H)
    (hs : s.val.val (0 : ℂ) = ∞) : (mobiusEndpointKernel H).index = 2 := by
  rw [mobiusEndpointKernel, Subgroup.index_eq_card, ← Nat.card_congr
    (MulAction.orbitEquivQuotientStabilizer H (((0 : ℂ) : Mobius.ExtendedComplex)))]
  change (MulAction.orbit H (((0 : ℂ) : Mobius.ExtendedComplex))).ncard = 2
  rw [mobiusEndpointKernel_exchange_orbit H hp s hs,
    Set.ncard_pair (OnePoint.coe_ne_infty (0 : ℂ))]

/-- A proper endpoint kernel has an actual endpoint-exchanging element. -/
theorem mobiusEndpointKernel_exists_exchange (H : Subgroup Mobius.complexMobiusGroup)
    (hp : H ≤ mobiusZeroInftyPairStabilizer) (hproper : mobiusEndpointKernel H ≠ ⊤) :
    ∃ s : H, s.val.val (0 : ℂ) = ∞ ∧ s.val.val ∞ = (0 : ℂ) := by
  have hs : ∃ s : H, s ∉ mobiusEndpointKernel H := by
    by_contra hn
    push Not at hn
    apply hproper
    ext s
    simp only [Subgroup.mem_top, iff_true]
    exact hn s
  obtain ⟨s, hs⟩ := hs
  rcases mobius_zeroInftyPair_cases ⟨s.val, hp s.property⟩ with hf | hf
  · exact False.elim (hs hf.1)
  · exact ⟨s, hf⟩

/-- The exact index-two conclusion follows whenever the endpoint kernel is proper. -/
theorem mobiusEndpointKernel_index_two_of_proper (H : Subgroup Mobius.complexMobiusGroup)
    (hp : H ≤ mobiusZeroInftyPairStabilizer) (hproper : mobiusEndpointKernel H ≠ ⊤) :
    (mobiusEndpointKernel H).index = 2 := by
  obtain ⟨s, hs, _⟩ := mobiusEndpointKernel_exists_exchange H hp hproper
  exact mobiusEndpointKernel_index_two H hp s hs

/-- A nonzero complex scaling can normalize any endpoint exchange to reciprocal. -/
theorem mobius_endpoint_exchange_normalize (f : Mobius.complexMobiusGroup)
    (hz : f.val (0 : ℂ) = ∞) (hi : f.val ∞ = (0 : ℂ)) :
    ∃ b : ℂˣ, Mobius.mobiusScaling b * f * (Mobius.mobiusScaling b)⁻¹ = mobiusReciprocal := by
  have hp : f ∈ mobiusZeroInftyPairStabilizer := by
    change f.val '' ({((0 : ℂ) : Mobius.ExtendedComplex), ∞} : Set Mobius.ExtendedComplex) = _
    simp only [Set.image_insert_eq, Set.image_singleton, hz, hi, Set.pair_comm]
  obtain ⟨a, ha | ha⟩ := mobius_zeroInftyPair_normal_form ⟨f, hp⟩
  · change f = Mobius.mobiusScaling a at ha
    rw [ha, mobiusScaling_zero] at hz
    exact False.elim ((OnePoint.coe_ne_infty (0 : ℂ)) hz)
  · change f = Mobius.mobiusScaling a * mobiusReciprocal at ha
    obtain ⟨z, hzsq⟩ := IsAlgClosed.exists_pow_nat_eq ((a : ℂ)⁻¹) (by decide : 0 < 2)
    have hz0 : z ≠ 0 := by
      intro he
      rw [he, zero_pow (by decide : 2 ≠ 0)] at hzsq
      exact (inv_ne_zero a.ne_zero) hzsq.symm
    let b : ℂˣ := Units.mk0 z hz0
    have hba : b * a * b = 1 := by
      apply Units.ext
      change z * (a : ℂ) * z = 1
      calc
        z * (a : ℂ) * z = z ^ 2 * (a : ℂ) := by ring
        _ = 1 := by rw [hzsq, inv_mul_cancel₀ a.ne_zero]
    refine ⟨b, ?_⟩
    rw [ha, mobiusScaling_inv]
    calc
      Mobius.mobiusScaling b * (Mobius.mobiusScaling a * mobiusReciprocal) * Mobius.mobiusScaling b⁻¹ =
          (Mobius.mobiusScaling b * Mobius.mobiusScaling a) * (mobiusReciprocal * Mobius.mobiusScaling b⁻¹) := by group
      _ = (Mobius.mobiusScaling b * Mobius.mobiusScaling a) * (Mobius.mobiusScaling b * mobiusReciprocal) := by
        rw [mobiusReciprocal_mul_scaling, inv_inv]
      _ = mobiusReciprocal := by
        rw [← mul_assoc, ← mobiusScaling_mul, ← mobiusScaling_mul, hba,
          mobiusScaling_one, one_mul]

/-- The pointwise endpoint stabilizer, viewed as a subgroup of the actual Mobius group. -/
def mobiusEndpointKernelImage (H : Subgroup Mobius.complexMobiusGroup) : Subgroup Mobius.complexMobiusGroup :=
  (mobiusEndpointKernel H).map H.subtype

/-- Its members remain in the original group. -/
theorem mobiusEndpointKernelImage_le (H : Subgroup Mobius.complexMobiusGroup) :
    mobiusEndpointKernelImage H ≤ H := by
  rintro f ⟨g, _, rfl⟩
  exact g.property

/-- The pointwise endpoint kernel fixes infinity. -/
theorem mobiusEndpointKernelImage_fixes_infty (H : Subgroup Mobius.complexMobiusGroup)
    (hp : H ≤ mobiusZeroInftyPairStabilizer) :
    mobiusEndpointKernelImage H ≤ Mobius.mobiusInftyStabilizer := by
  rintro f ⟨g, hg, rfl⟩
  exact mobiusEndpointKernel_fixes_infty H hp ⟨g, hg⟩

/-- It also fixes zero. -/
theorem mobiusEndpointKernelImage_fixes_zero (H : Subgroup Mobius.complexMobiusGroup)
    (f : Mobius.complexMobiusGroup) (hf : f ∈ mobiusEndpointKernelImage H) : f.val (0 : ℂ) = (0 : ℂ) := by
  rcases hf with ⟨g, hg, rfl⟩
  exact hg

/-- The pointwise endpoint kernel of a discrete group is discrete. -/
theorem mobiusEndpointKernelImage_discrete (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) : Mobius.IsDiscreteMobiusSubgroup (mobiusEndpointKernelImage H) := by
  exact isDiscrete_iff_discreteTopology.mp
    ((isDiscrete_iff_discreteTopology.mpr hH).mono (mobiusEndpointKernelImage_le H))

/-- A reciprocal-containing pair stabilizer has the exact two-family normal form. -/
theorem discretePair_reciprocal_normal_form (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hp : H ≤ mobiusZeroInftyPairStabilizer)
    (hrec : mobiusReciprocal ∈ H) :
    ∃ w a : ℂˣ, ∃ q : ℕ, 0 < q ∧ ‖(w : ℂ)‖ = 1 ∧ w ^ q = 1 ∧
      ∀ f : Mobius.complexMobiusGroup, f ∈ H ↔ ∃ k : Fin q, ∃ n : ℤ,
        f = Mobius.mobiusScaling (w ^ (k : ℕ) * a ^ n) ∨
          f = Mobius.mobiusScaling (w ^ (k : ℕ) * a ^ n) * mobiusReciprocal := by
  let L := mobiusEndpointKernelImage H
  obtain ⟨w, a, q, hq, hwn, hwq, hform⟩ := discreteDilation_scaling_normal_form L
    (mobiusEndpointKernelImage_discrete H hH) (mobiusEndpointKernelImage_fixes_infty H hp)
    (mobiusEndpointKernelImage_fixes_zero H)
  refine ⟨w, a, q, hq, hwn, hwq, ?_⟩
  intro f
  constructor
  · intro hf
    rcases mobius_zeroInftyPair_cases ⟨f, hp hf⟩ with hfix | hswap
    · have hfL : f ∈ L := ⟨⟨f, hf⟩, hfix.1, rfl⟩
      obtain ⟨k, n, he⟩ := (hform f).mp hfL
      exact ⟨k, n, Or.inl he⟩
    · have hfr : f * mobiusReciprocal ∈ H := H.mul_mem hf hrec
      have hfr0 : (f * mobiusReciprocal).val (0 : ℂ) = (0 : ℂ) := by
        change f.val (mobiusReciprocal.val (0 : ℂ)) = (0 : ℂ)
        rw [mobiusReciprocal_zero]
        exact hswap.2
      have hfrL : f * mobiusReciprocal ∈ L := ⟨⟨f * mobiusReciprocal, hfr⟩, hfr0, rfl⟩
      obtain ⟨k, n, he⟩ := (hform _).mp hfrL
      refine ⟨k, n, Or.inr ?_⟩
      rw [← he, mul_assoc, mobiusReciprocal_mul_self, mul_one]
  · rintro ⟨k, n, he | he⟩
    · subst f
      exact mobiusEndpointKernelImage_le H ((hform _).mpr ⟨k, n, rfl⟩)
    · subst f
      exact H.mul_mem (mobiusEndpointKernelImage_le H ((hform _).mpr ⟨k, n, rfl⟩)) hrec

/-- Endpoint exchange is normalized by a scaling without moving either endpoint. -/
theorem discretePair_normalize_reciprocal (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hp : H ≤ mobiusZeroInftyPairStabilizer)
    (hproper : mobiusEndpointKernel H ≠ ⊤) :
    ∃ b : ℂˣ, Mobius.IsDiscreteMobiusSubgroup (DiscreteGroups.Action.Actions.subgroupConjugate
      (Mobius.mobiusScaling b) H) ∧
      DiscreteGroups.Action.Actions.subgroupConjugate (Mobius.mobiusScaling b) H ≤ mobiusZeroInftyPairStabilizer ∧
        mobiusReciprocal ∈ DiscreteGroups.Action.Actions.subgroupConjugate (Mobius.mobiusScaling b) H := by
  obtain ⟨s, hsz, hsi⟩ := mobiusEndpointKernel_exists_exchange H hp hproper
  obtain ⟨b, hb⟩ := mobius_endpoint_exchange_normalize s.val hsz hsi
  refine ⟨b, ?_, ?_, ?_⟩
  · let discreteDilationOriginal : DiscreteTopology H := hH
    exact DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete (Mobius.mobiusScaling b) H
  · rintro f ⟨g, hg, rfl⟩
    exact mobiusZeroInftyPairStabilizer.mul_mem
      (mobiusZeroInftyPairStabilizer.mul_mem (mobiusScaling_mem_zeroInftyPairStabilizer b) (hp hg))
      (mobiusZeroInftyPairStabilizer.inv_mem (mobiusScaling_mem_zeroInftyPairStabilizer b))
  · exact ⟨s.val, s.property, hb⟩

/-- The genuine discrete pair-preserving extension has the source's two-family formula after conjugacy. -/
theorem discretePair_index_two_classification (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hp : H ≤ mobiusZeroInftyPairStabilizer)
    (hproper : mobiusEndpointKernel H ≠ ⊤) :
    (mobiusEndpointKernel H).index = 2 ∧ ∃ b w a : ℂˣ, ∃ q : ℕ,
      0 < q ∧ ‖(w : ℂ)‖ = 1 ∧ w ^ q = 1 ∧
        ∀ f : Mobius.complexMobiusGroup,
          f ∈ DiscreteGroups.Action.Actions.subgroupConjugate (Mobius.mobiusScaling b) H ↔ ∃ k : Fin q, ∃ n : ℤ,
            f = Mobius.mobiusScaling (w ^ (k : ℕ) * a ^ n) ∨
              f = Mobius.mobiusScaling (w ^ (k : ℕ) * a ^ n) * mobiusReciprocal := by
  refine ⟨mobiusEndpointKernel_index_two_of_proper H hp hproper, ?_⟩
  obtain ⟨b, hdisc, hpair, hrec⟩ := discretePair_normalize_reciprocal H hH hp hproper
  obtain ⟨w, a, q, hq, hwn, hwq, hall⟩ :=
    discretePair_reciprocal_normal_form _ hdisc hpair hrec
  exact ⟨b, w, a, q, hq, hwn, hwq, hall⟩

/-- The modulus homomorphism takes values in the positive real units. -/
theorem dilationModulusHom_positive (H : Subgroup Mobius.complexMobiusGroup)
    (hi : H ≤ Mobius.mobiusInftyStabilizer) (f : H) : (0 : ℝ) < (dilationModulusHom H hi f : ℝ) :=
  norm_pos_iff.mpr (Units.ne_zero _)

/-- A discrete dilation subgroup is finite cyclic or contains a genuine loxodromic map. -/
theorem discreteDilation_finite_cyclic_or_loxodromic (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ)) :
    (Finite H ∧ IsCyclic H) ∨ ∃ f ∈ H, Mobius.MobiusLoxodromic f := by
  by_cases hall : ∀ f : H, ‖((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)‖ = 1
  · exact Or.inl (discreteDilation_unit_moduli_finite_cyclic H hH hi hz hall)
  · push Not at hall
    obtain ⟨f, hf⟩ := hall
    exact Or.inr ⟨f.val, f.property, dilation_loxodromic_of_modulus_ne_one H hi hz f hf⟩

/-- Even endpoint-exchanging pair-preservers cannot be parabolic. -/
theorem mobiusPair_no_parabolic (f : Mobius.complexMobiusGroup)
    (hp : f ∈ mobiusZeroInftyPairStabilizer) : ¬Mobius.MobiusParabolic f := by
  rcases mobius_zeroInftyPair_cases ⟨f, hp⟩ with hfix | hswap
  · rintro ⟨_, a, ha⟩
    exact (OnePoint.coe_ne_infty (0 : ℂ)) (((ha _).mp hfix.1).trans ((ha _).mp hfix.2).symm)
  · intro hf
    have hs : f ^ 2 = 1 := by
      simpa only [pow_two] using mobius_endpoint_exchange_square f hswap.1 hswap.2
    have ho : IsOfFinOrder f := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hs⟩
    exact (Mobius.mobius_finite_order_elliptic f hf.1 ho).not_parabolic hf

/-- Arbitrary distinct common boundary fixed points admit the genuine dilation normal form after conjugacy. -/
theorem discreteDilation_arbitrary_fixed_pair_normal_form (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (a b : Mobius.ExtendedComplex) (hab : a ≠ b)
    (hfix : ∀ f ∈ H, f.val a = a ∧ f.val b = b) :
    ∃ u : Mobius.complexMobiusGroup, ∃ w c : ℂˣ, ∃ q : ℕ,
      u.val a = (0 : ℂ) ∧ u.val b = ∞ ∧
        0 < q ∧ ‖(w : ℂ)‖ = 1 ∧ w ^ q = 1 ∧
          ∀ f : Mobius.complexMobiusGroup, f ∈ DiscreteGroups.Action.Actions.subgroupConjugate u H ↔
            ∃ k : Fin q, ∃ n : ℤ, f = Mobius.mobiusScaling (w ^ (k : ℕ) * c ^ n) := by
  obtain ⟨u, hua, hub⟩ := mobius_exists_send_pair_zero_infty a b hab
  let K := DiscreteGroups.Action.Actions.subgroupConjugate u H
  have hK : Mobius.IsDiscreteMobiusSubgroup K := by
    let discreteDilationArbitraryOriginal : DiscreteTopology H := hH
    exact DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete u H
  have hKi : K ≤ Mobius.mobiusInftyStabilizer :=
    mobius_subgroupConjugate_le_inftyStabilizer H b (fun f => (hfix f.val f.property).2) u hub
  have hKz : ∀ f ∈ K, f.val (0 : ℂ) = (0 : ℂ) := by
    rintro f ⟨g, hg, rfl⟩
    change (u * g * u⁻¹).val ((0 : ℂ) : Mobius.ExtendedComplex) = ((0 : ℂ) : Mobius.ExtendedComplex)
    rw [← hua]
    exact mobius_conjugate_fixedpoint g u a (hfix g hg).1
  obtain ⟨w, c, q, hq, hwn, hwq, hall⟩ := discreteDilation_scaling_normal_form K hK hKi hKz
  exact ⟨u, w, c, q, hua, hub, hq, hwn, hwq, hall⟩

/-- Consecutive genuine subgroup conjugations compose in their group multiplication order. -/
theorem dilation_subgroupConjugate_compose {G : Type*} [Group G]
    (u v : G) (H : Subgroup G) :
    DiscreteGroups.Action.Actions.subgroupConjugate u (DiscreteGroups.Action.Actions.subgroupConjugate v H) =
      DiscreteGroups.Action.Actions.subgroupConjugate (u * v) H := by
  change (H.map (MulAut.conj v).toMonoidHom).map (MulAut.conj u).toMonoidHom =
    H.map (MulAut.conj (u * v)).toMonoidHom
  rw [Subgroup.map_map]
  congr 1
  ext f
  change u * (v * f * v⁻¹) * u⁻¹ = (u * v) * f * (u * v)⁻¹
  group

/-- The complete dilation or index-two reciprocal formula for any preserved pair of boundary points. -/
theorem discreteMobius_invariant_pair_normal_forms (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (a b : Mobius.ExtendedComplex) (hab : a ≠ b)
    (hpair : ∀ f : H, f.val.val '' {a, b} = {a, b}) :
    ∃ u : Mobius.complexMobiusGroup, ∃ w c : ℂˣ, ∃ q : ℕ,
      0 < q ∧ ‖(w : ℂ)‖ = 1 ∧ w ^ q = 1 ∧
        ((∀ f : Mobius.complexMobiusGroup, f ∈ DiscreteGroups.Action.Actions.subgroupConjugate u H ↔
            ∃ k : Fin q, ∃ n : ℤ, f = Mobius.mobiusScaling (w ^ (k : ℕ) * c ^ n)) ∨
          ((mobiusEndpointKernel (DiscreteGroups.Action.Actions.subgroupConjugate u H)).index = 2 ∧
            ∀ f : Mobius.complexMobiusGroup, f ∈ DiscreteGroups.Action.Actions.subgroupConjugate u H ↔ ∃ k : Fin
              q, ∃ n : ℤ,
              f = Mobius.mobiusScaling (w ^ (k : ℕ) * c ^ n) ∨
                f = Mobius.mobiusScaling (w ^ (k : ℕ) * c ^ n) * mobiusReciprocal)) := by
  obtain ⟨v, hv⟩ := mobius_invariant_pair_conjugate_zeroInftyPairStabilizer H a b hab hpair
  let K := DiscreteGroups.Action.Actions.subgroupConjugate v H
  have hK : Mobius.IsDiscreteMobiusSubgroup K := by
    let discreteDilationPairOriginal : DiscreteTopology H := hH
    exact DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete v H
  by_cases hproper : mobiusEndpointKernel K = ⊤
  · have hKz : ∀ f ∈ K, f.val (0 : ℂ) = (0 : ℂ) := by
      intro f hf
      have hmem : (⟨f, hf⟩ : K) ∈ mobiusEndpointKernel K := by rw [hproper]; trivial
      exact hmem
    have hKi : K ≤ Mobius.mobiusInftyStabilizer := by
      intro f hf
      rcases mobius_zeroInftyPair_cases ⟨f, hv hf⟩ with hfix | hswap
      · exact hfix.2
      · exact False.elim ((OnePoint.coe_ne_infty (0 : ℂ)) ((hKz f hf).symm.trans hswap.1))
    obtain ⟨w, c, q, hq, hwn, hwq, hall⟩ := discreteDilation_scaling_normal_form K hK hKi hKz
    exact ⟨v, w, c, q, hq, hwn, hwq, Or.inl hall⟩
  · obtain ⟨d, hdisc, hstable, hrec⟩ := discretePair_normalize_reciprocal K hK hv hproper
    obtain ⟨w, c, q, hq, hwn, hwq, hall⟩ :=
      discretePair_reciprocal_normal_form _ hdisc hstable hrec
    have hind := mobiusEndpointKernel_index_two _ hstable
      ⟨mobiusReciprocal, hrec⟩ mobiusReciprocal_zero
    refine ⟨Mobius.mobiusScaling d * v, w, c, q, hq, hwn, hwq, Or.inr ?_⟩
    rw [← dilation_subgroupConjugate_compose]
    exact ⟨hind, hall⟩

end LowDimensionalTopology.Geometry.DiscreteGroups
