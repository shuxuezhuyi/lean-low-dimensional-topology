module

public import LowDimensionalTopology.Geometry.Teichmuller.PoincareKernelSeries
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchyCosets
public import LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.BigOperators.Group.Finset.Interval
public import Mathlib.Order.Filter.AtTopBot.Interval
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The full-period length kernel and its projective Poincare series

The same three-pole kernel has a genuine bilateral cyclic sum. The actual
projective group is then partitioned by the given right-coset section, retaining
the full multiplier and the entire ineffective special-linear kernel. The
existing integrable Poincare theorem gives the resulting coefficient pairing.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter Topology MeasureTheory
open scoped UpperHalfPlane OnePoint ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

private def lengthSeed (s : ℝ) (z : ℂ) : ℂ :=
  LiZhongQC.ahKer (Real.exp (2 * s) : ℂ) z / (Real.exp (2 * s) : ℂ)

private theorem halfPlane_sub_real_ne_zero {z : ℂ}
    (hz : z ∈ LiZhongQC.upperHalf) (r : ℝ) : z - (r : ℂ) ≠ 0 := by
  intro he
  have him := congrArg Complex.im (sub_eq_zero.mp he)
  simp only [Complex.ofReal_im] at him
  exact (ne_of_gt hz) him

private theorem lengthSeed_integrable (s : ℝ) : Integrable (lengthSeed s) :=
  (LiZhongQC.ah_ker_integrable (Real.exp (2 * s) : ℂ)).div_const _

private theorem lengthSeed_differentiableOn (s : ℝ) :
    DifferentiableOn ℂ (lengthSeed s) LiZhongQC.upperHalf := by
  intro z hz
  have hz0 : z ≠ 0 := by
    simpa only [Complex.ofReal_zero, sub_zero] using halfPlane_sub_real_ne_zero hz 0
  have hz1 : z - 1 ≠ 0 := by
    simpa only [Complex.ofReal_one] using halfPlane_sub_real_ne_zero hz 1
  have hden : z * (z - 1) * (z - (Real.exp (2 * s) : ℂ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hz0 hz1)
      (halfPlane_sub_real_ne_zero hz (Real.exp (2 * s)))
  exact (((differentiableAt_const _).div
    ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
      (differentiableAt_id.sub_const (Real.exp (2 * s) : ℂ))) hden).div_const
        (Real.exp (2 * s) : ℂ)).differentiableWithinAt

private theorem lengthSeed_area (s : ℝ) :
    LiZhongQC.phiArea (lengthSeed s) LiZhongQC.upperHalf < ⊤ := by
  simpa only [LiZhongQC.phiArea, HasFiniteIntegral, ofReal_norm] using
    (lengthSeed_integrable s).integrableOn.hasFiniteIntegral

private theorem projective_action_mul (Γ : Subgroup Deck)
    (g h : Γ.map Hyperbolic.realSLMobius) {z : ℂ}
    (hz : z ∈ LiZhongQC.upperHalf) :
    ProjectivePoincare.action Γ (g * h) z =
      ProjectivePoincare.action Γ g (ProjectivePoincare.action Γ h z) := by
  obtain ⟨A, rfl⟩ := ProjectivePoincare.imageHom_surjective Γ g
  obtain ⟨B, rfl⟩ := ProjectivePoincare.imageHom_surjective Γ h
  rw [← (ProjectivePoincare.imageHom Γ).map_mul,
    ProjectivePoincare.action_image Γ (A * B) hz,
    ProjectivePoincare.action_image Γ B hz,
    ProjectivePoincare.action_image Γ A (LiZhongQC.h36p_m_mem B.val hz),
    Subgroup.coe_mul, LiZhongQC.h36p_b_m_mul A.val B.val hz]

private theorem dilation_power_action (Γ : Subgroup Deck) (A : Γ) (s : ℝ)
    (hA : Hyperbolic.realSLMobius A.val =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s)) (n : ℤ)
    {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    ProjectivePoincare.action Γ ((ProjectivePoincare.imageHom Γ A) ^ n) z =
      (Real.exp (2 * s) : ℂ) ^ n * z := by
  have he : Hyperbolic.realSLMobius A.val ^ n =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL ((n : ℝ) * s)) := by
    rw [hA, ← map_zpow, Fuchsian.hLogDilationSL_zpow]
  change (((Hyperbolic.realSLMobius A.val) ^ n).val (z : Mobius.ExtendedComplex)).elim 0 id = _
  rw [he, Hyperbolic.realSLMobius_action _ (⟨z, hz⟩ : ℍ),
    OnePoint.elim_some, id_eq, Fuchsian.hLogDilationSL_coe]
  congr 1
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

private theorem dilation_power_hasDerivAt (Γ : Subgroup Deck) (A : Γ) (s : ℝ)
    (hA : Hyperbolic.realSLMobius A.val =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s)) (n : ℤ)
    {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    HasDerivAt (ProjectivePoincare.action Γ ((ProjectivePoincare.imageHom Γ A) ^ n))
      ((Real.exp (2 * s) : ℂ) ^ n) z := by
  have h : HasDerivAt (fun w : ℂ => (Real.exp (2 * s) : ℂ) ^ n * w)
      ((Real.exp (2 * s) : ℂ) ^ n) z := by
    exact hasDerivAt_const_mul ((Real.exp (2 * s) : ℂ) ^ n)
  apply h.congr_of_eventuallyEq
  filter_upwards [LiZhongQC.isOpen_upperHalf.mem_nhds hz] with w hw
  exact dilation_power_action Γ A s hA n hw

private theorem dilation_power_injective (Γ : Subgroup Deck) (A : Γ)
    (s : ℝ) (hs : 0 < s)
    (hA : Hyperbolic.realSLMobius A.val =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s)) :
    Function.Injective (fun n : ℤ => (ProjectivePoincare.imageHom Γ A) ^ n) := by
  intro n k he
  have hi : (Complex.I : ℂ) ∈ LiZhongQC.upperHalf := by
    simpa only [LiZhongQC.upperHalf, Set.mem_ofPred_eq, Complex.I_im] using
      (zero_lt_one : (0 : ℝ) < 1)
  have hp := congrArg (fun g => ProjectivePoincare.action Γ g Complex.I) he
  rw [dilation_power_action Γ A s hA n hi,
    dilation_power_action Γ A s hA k hi] at hp
  have hn : (Real.exp (2 * s) : ℝ) ^ n = Real.exp (2 * s) ^ k := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_zpow] using mul_right_cancel₀ Complex.I_ne_zero hp
  exact (zpow_right_strictMono₀
    (Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) hs))).injective hn

private theorem power_mul_term (Γ : Subgroup Deck) (A : Γ) (s : ℝ)
    (hA : Hyperbolic.realSLMobius A.val =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))
    (n : ℤ) (g : Γ.map Hyperbolic.realSLMobius) {z : ℂ}
    (hz : z ∈ LiZhongQC.upperHalf) :
    ProjectivePoincare.term Γ (lengthSeed s)
      ((ProjectivePoincare.imageHom Γ A) ^ n * g) z =
      ((Real.exp (2 * s) : ℂ) ^ n) ^ 2 *
        lengthSeed s ((Real.exp (2 * s) : ℂ) ^ n * ProjectivePoincare.action Γ g z) *
          (deriv (ProjectivePoincare.action Γ g) z) ^ 2 := by
  obtain ⟨B, rfl⟩ := ProjectivePoincare.imageHom_surjective Γ g
  have hg := (ProjectivePoincare.action_hasDerivAt_image Γ B hz)
  have hd := (hg.const_mul ((Real.exp (2 * s) : ℂ) ^ n)).congr_of_eventuallyEq
    (show ProjectivePoincare.action Γ
        ((ProjectivePoincare.imageHom Γ A) ^ n * ProjectivePoincare.imageHom Γ B)
      =ᶠ[𝓝 z] (fun w => (Real.exp (2 * s) : ℂ) ^ n *
        ProjectivePoincare.action Γ (ProjectivePoincare.imageHom Γ B) w) from by
      filter_upwards [LiZhongQC.isOpen_upperHalf.mem_nhds hz] with w hw
      rw [projective_action_mul Γ _ _ hw,
        dilation_power_action Γ A s hA n (ProjectivePoincare.action_mem Γ _ hw)])
  rw [ProjectivePoincare.term, projective_action_mul Γ _ _ hz,
    dilation_power_action Γ A s hA n (ProjectivePoincare.action_mem Γ _ hz),
    hd.deriv, hg.deriv]
  ring

private theorem cyclic_lengthSeed_hasSum (Γ : Subgroup Deck) (hΓ : LiZhongQC.IsFuchsian Γ)
    (A : Γ) (s : ℝ) (hs : 0 < s)
    (hA : Hyperbolic.realSLMobius A.val =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))
    {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    HasSum (fun n : ℤ => ((Real.exp (2 * s) : ℂ) ^ n) ^ 2 *
      lengthSeed s ((Real.exp (2 * s) : ℂ) ^ n * z)) (-(1 / z ^ 2)) := by
  let lam := Real.exp (2 * s)
  let b : ℤ → ℂ := fun n => (lam : ℂ) ^ n / ((lam : ℂ) ^ n * z - 1)
  let t : ℤ → ℂ := fun n => ((lam : ℂ) ^ n) ^ 2 * lengthSeed s ((lam : ℂ) ^ n * z)
  have hlam : 1 < lam := Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) hs)
  have hlam0 : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans hlam))
  have hz0 : z ≠ 0 := by
    simpa only [Complex.ofReal_zero, sub_zero] using halfPlane_sub_real_ne_zero hz 0
  have hmem (n : ℤ) : (lam : ℂ) ^ n * z ∈ LiZhongQC.upperHalf := by
    change 0 < ((lam : ℂ) ^ n * z).im
    rw [← Complex.ofReal_zpow]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos (zpow_pos (zero_lt_one.trans hlam) n) hz
  have hnorm : Summable (fun n : ℤ => ‖t n‖) := by
    have h := (ProjectivePoincare.summable_norm Γ hΓ (lengthSeed_differentiableOn s)
      (lengthSeed_area s) hz).comp_injective (dilation_power_injective Γ A s hs hA)
    refine h.congr (fun n => ?_)
    change ‖lengthSeed s (ProjectivePoincare.action Γ
      ((ProjectivePoincare.imageHom Γ A) ^ n) z) *
        (deriv (ProjectivePoincare.action Γ ((ProjectivePoincare.imageHom Γ A) ^ n)) z) ^ 2‖ = ‖t n‖
    rw [dilation_power_action Γ A s hA n hz,
      (dilation_power_hasDerivAt Γ A s hA n hz).deriv]
    dsimp only [t, lam]
    congr 1
    ring
  have hstep (n : ℤ) : t n = (1 / z) * (b (n - 1) - b n) := by
    have hn0 := zpow_ne_zero n hlam0
    have h1 : (lam : ℂ) ^ n * z - 1 ≠ 0 := by
      simpa only [Complex.ofReal_one] using halfPlane_sub_real_ne_zero (hmem n) 1
    have hl := halfPlane_sub_real_ne_zero (hmem n) lam
    have hm1 : (lam : ℂ) ^ (n - 1) * z - 1 ≠ 0 := by
      simpa only [Complex.ofReal_one] using halfPlane_sub_real_ne_zero (hmem (n - 1)) 1
    dsimp only [t, b, lengthSeed, LiZhongQC.ahKer]
    change ((lam : ℂ) ^ n) ^ 2 *
      ((lam : ℂ) * ((lam : ℂ) - 1) /
        ((lam : ℂ) ^ n * z * ((lam : ℂ) ^ n * z - 1) *
          ((lam : ℂ) ^ n * z - (lam : ℂ))) / (lam : ℂ)) = _
    rw [zpow_sub_one₀ hlam0] at hm1 ⊢
    field_simp [hlam0, hn0, hz0, h1, hl, hm1] ; ring
  have hsum (N : ℕ) : (∑ n ∈ Finset.Icc (-(N : ℤ)) N, t n) =
      (1 / z) * (b (-(N : ℤ) - 1) - b N) := by
    have hi := Finset.sum_Ico_int_sub N (fun n : ℤ => b (n - 1))
    have he : (∑ n ∈ Finset.Ico (-(N : ℤ)) N, t n) =
        (1 / z) * (b (-(N : ℤ) - 1) - b ((N : ℤ) - 1)) := by
      rw [← hi, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => by simpa only [add_sub_cancel_right] using hstep n)
    rw [Finset.sum_Icc_eq_sum_Ico_add t
      ((neg_nonpos.mpr (Int.natCast_nonneg N)).trans (Int.natCast_nonneg N)), he, hstep]
    ring
  have hinv : Tendsto (fun N : ℕ => ((lam : ℂ)⁻¹) ^ N) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (zero_lt_one.trans hlam).le)
        ((inv_lt_one₀ (zero_lt_one.trans hlam)).mpr hlam))
    simpa only [Function.comp_def, Complex.ofReal_pow, Complex.ofReal_inv,
      Complex.ofReal_zero] using h
  have hpos : Tendsto (fun N : ℕ => b N) atTop (𝓝 (1 / z)) := by
    have h : Tendsto (fun N : ℕ => (1 : ℂ) / (z - ((lam : ℂ)⁻¹) ^ N))
        atTop (𝓝 (1 / z)) := by
      simpa only [Pi.div_def, sub_zero] using tendsto_const_nhds.div
        (tendsto_const_nhds.sub hinv) (by simpa only [sub_zero] using hz0)
    refine Filter.Tendsto.congr (fun N => ?_) h
    have h1 : (lam : ℂ) ^ (N : ℤ) * z - 1 ≠ 0 := by
      simpa only [Complex.ofReal_one] using halfPlane_sub_real_ne_zero (hmem (N : ℤ)) 1
    rw [zpow_natCast] at h1
    have h2 : z - ((lam : ℂ)⁻¹) ^ N ≠ 0 := by
      simpa only [Complex.ofReal_pow, Complex.ofReal_inv] using
        halfPlane_sub_real_ne_zero hz ((lam⁻¹) ^ N)
    dsimp only [b]
    rw [zpow_natCast]
    apply (div_eq_div_iff h2 h1).2
    rw [one_mul, mul_sub, inv_pow, mul_inv_cancel₀ (pow_ne_zero N hlam0)]
  have hneg : Tendsto (fun N : ℕ => b (-(N : ℤ) - 1)) atTop (𝓝 0) := by
    have hx := hinv.const_mul ((lam : ℂ)⁻¹)
    have h := hx.div ((hx.mul_const z).sub_const 1) (by norm_num)
    simp only [mul_zero, zero_mul, zero_sub, zero_div] at h
    refine Filter.Tendsto.congr (fun N => ?_) h
    dsimp only [b]
    rw [Pi.div_apply, zpow_sub_one₀ hlam0, zpow_neg, zpow_natCast]
    simp only [inv_pow]
    congr 1 <;> ring
  have hlimit : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, t n)
      atTop (𝓝 (-(1 / z ^ 2))) := by
    have h := (hneg.sub hpos).const_mul (1 / z)
    have he : (1 / z) * (0 - 1 / z) = -(1 / z ^ 2) := by
      field_simp [hz0] ; ring
    rw [he] at h
    exact Filter.Tendsto.congr (fun N => (hsum N).symm) h
  exact hasSum_of_subseq_of_summable hnorm Finset.tendsto_Icc_neg hlimit

/-- Every actual projective cyclic fiber has its true full-period sum and
absolute convergence; no convergence premise is added. -/
theorem lengthKernel_cyclic_hasSum
    (Γ : Subgroup Deck) (hΓ : LiZhongQC.IsFuchsian Γ)
    (A0 : Deck) (hA0 : A0 ∈ Γ) (s : ℝ) (hs : 0 < s)
    (hproj : Hyperbolic.realSLMobius A0 =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s)) :
    let f : ℂ → ℂ := fun ζ =>
      LiZhongQC.ahKer (Real.exp (2 * s) : ℂ) ζ / (Real.exp (2 * s) : ℂ)
    let δ := ProjectivePoincare.imageHom Γ ⟨A0, hA0⟩
    ∀ (g : Γ.map Hyperbolic.realSLMobius) (z : ℂ), z ∈ LiZhongQC.upperHalf →
      HasSum (fun n : ℤ => ProjectivePoincare.term Γ f (δ ^ n * g) z)
        (-((deriv (ProjectivePoincare.action Γ g) z /
          ProjectivePoincare.action Γ g z) ^ 2)) ∧
      Summable (fun n : ℤ => ‖ProjectivePoincare.term Γ f (δ ^ n * g) z‖) := by
  dsimp only
  intro g z hz
  let A : Γ := ⟨A0, hA0⟩
  have hw := ProjectivePoincare.action_mem Γ g hz
  have hw0 : ProjectivePoincare.action Γ g z ≠ 0 := by
    simpa only [Complex.ofReal_zero, sub_zero] using halfPlane_sub_real_ne_zero hw 0
  have hsum := (cyclic_lengthSeed_hasSum Γ hΓ A s hs hproj hw).mul_right
    ((deriv (ProjectivePoincare.action Γ g) z) ^ 2)
  have hnorm := (ProjectivePoincare.summable_norm Γ hΓ (lengthSeed_differentiableOn s)
    (lengthSeed_area s) hz).comp_injective
      (i := fun n : ℤ => (ProjectivePoincare.imageHom Γ A) ^ n * g)
      (fun n k he => dilation_power_injective Γ A s hs hproj (mul_right_cancel he))
  refine ⟨?_, hnorm⟩
  have he : -(1 / ProjectivePoincare.action Γ g z ^ 2) *
      (deriv (ProjectivePoincare.action Γ g) z) ^ 2 =
        -((deriv (ProjectivePoincare.action Γ g) z / ProjectivePoincare.action Γ g z) ^ 2) := by
    field_simp [hw0]
  rw [he] at hsum
  exact hsum.congr_fun (fun n => power_mul_term Γ A s hproj n g hz)

private def rightCosetPowerEquiv (Γ : Subgroup Deck) (A : Γ) (s : ℝ) (hs : 0 < s)
    (hA : Hyperbolic.realSLMobius A.val =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))
    (ρ : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)) → Γ)
    (hρ : ∀ u, Quotient.mk _ (ρ u) = u) :
    (Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))) × ℤ ≃
      Γ.map Hyperbolic.realSLMobius := by
  classical
  let δ := ProjectivePoincare.imageHom Γ A
  let r := fun p : (Quotient (QuotientGroup.rightRel
      (projectiveDilationSubgroup Γ s))) × ℤ =>
    δ ^ p.2 * ProjectivePoincare.imageHom Γ (ρ p.1)
  refine Equiv.ofBijective r ⟨?_, ?_⟩
  · rintro ⟨u, n⟩ ⟨v, k⟩ he
    have hv : ProjectivePoincare.imageHom Γ (ρ v) =
        δ ^ (n - k) * ProjectivePoincare.imageHom Γ (ρ u) := by
      calc
        _ = (δ ^ k)⁻¹ * (δ ^ k * ProjectivePoincare.imageHom Γ (ρ v)) := by
          rw [inv_mul_cancel_left]
        _ = (δ ^ k)⁻¹ * (δ ^ n * ProjectivePoincare.imageHom Γ (ρ u)) := by
          rw [show δ ^ k * ProjectivePoincare.imageHom Γ (ρ v) =
            δ ^ n * ProjectivePoincare.imageHom Γ (ρ u) from he.symm]
        _ = _ := by
          rw [← mul_assoc, ← zpow_neg, ← zpow_add]
          congr 2
          ring
    have hdiff : Hyperbolic.realSLMobius ((ρ v).val * (ρ u).val⁻¹) =
        Hyperbolic.realSLMobius A.val ^ (n - k) := by
      have h := congrArg Subtype.val hv
      change Hyperbolic.realSLMobius (ρ v).val =
        Hyperbolic.realSLMobius A.val ^ (n - k) *
          Hyperbolic.realSLMobius (ρ u).val at h
      rw [map_mul, map_inv, h, mul_inv_cancel_right]
    have hmem : ρ v * (ρ u)⁻¹ ∈ projectiveDilationSubgroup Γ s := by
      change Hyperbolic.realSLMobius ((ρ v).val * (ρ u).val⁻¹) ∈
        Subgroup.zpowers (Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))
      rw [hdiff, hA]
      exact Subgroup.mem_zpowers_iff.mpr ⟨n - k, rfl⟩
    have huv : u = v := by
      rw [← hρ u, ← hρ v]
      exact Quotient.sound (QuotientGroup.rightRel_apply.mpr hmem)
    subst v
    have hnk : n = k := dilation_power_injective Γ A s hs hA (mul_right_cancel he)
    exact Prod.ext rfl hnk
  · intro g
    obtain ⟨γ, rfl⟩ := ProjectivePoincare.imageHom_surjective Γ g
    let u := Quotient.mk (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)) γ
    have hrel : QuotientGroup.rightRel (projectiveDilationSubgroup Γ s) (ρ u) γ :=
      Quotient.exact (hρ u)
    have hmem := QuotientGroup.rightRel_apply.mp hrel
    change Hyperbolic.realSLMobius (γ.val * (ρ u).val⁻¹) ∈
      Subgroup.zpowers (Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s)) at hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨(u, n), ?_⟩
    apply Subtype.ext
    change Hyperbolic.realSLMobius A.val ^ n *
      Hyperbolic.realSLMobius (ρ u).val = Hyperbolic.realSLMobius γ.val
    rw [hA, hn, map_mul, map_inv, inv_mul_cancel_right]

private theorem image_squaredLogDeriv (Γ : Subgroup Deck) (γ : Γ)
    {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    (deriv (ProjectivePoincare.action Γ (ProjectivePoincare.imageHom Γ γ)) z /
      ProjectivePoincare.action Γ (ProjectivePoincare.imageHom Γ γ) z) ^ 2 =
    (deriv (LiZhongQC.mobiusFn (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1)) z /
      LiZhongQC.mobiusFn (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1) z) ^ 2 := by
  change _ = (deriv (LiZhongQC.h36p_m γ.val) z / LiZhongQC.h36p_m γ.val z) ^ 2
  rw [(ProjectivePoincare.action_hasDerivAt_image Γ γ hz).deriv,
    ProjectivePoincare.action_image Γ γ hz, (LiZhongQC.h36p_m_hasDerivAt γ.val hz).deriv]

/-- The same actual full-period right-coset series has a genuine HasSum,
is integrable automorphic, and gives the literal native coefficient pairing.
The true ineffective matrix multiplicity is retained and then canceled. -/
theorem lengthKernel_relative_poincare
    (Γ : Subgroup Deck) (hΓ : LiZhongQC.IsFuchsian Γ)
    (A0 : Deck) (hA0 : A0 ∈ Γ) (s : ℝ) (hs : 0 < s)
    (hproj : Hyperbolic.realSLMobius A0 =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s)) :
    let f : ℂ → ℂ := fun ζ =>
      LiZhongQC.ahKer (Real.exp (2 * s) : ℂ) ζ / (Real.exp (2 * s) : ℂ)
    let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
    let m : Γ → ℂ → ℂ := fun γ =>
      LiZhongQC.mobiusFn (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1)
    let mult := Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1))
    ∀ (ρ : C → Γ), (∀ u : C, Quotient.mk _ (ρ u) = u) →
      let Θ : ℂ → ℂ := fun z => ∑' u : C, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2
      (∀ z : ℂ, z ∈ LiZhongQC.upperHalf →
        HasSum (fun u : C => (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
          (-ProjectivePoincare.series Γ f z) ∧
        Summable (fun u : C => ‖(deriv (m (ρ u)) z / m (ρ u) z) ^ 2‖) ∧
        LiZhongQC.h36p_theta Γ f z = -(mult : ℂ) * Θ z) ∧
      ∀ (F : Set ℂ), LiZhongQC.IsFundamentalDomainH Γ F →
        Θ ∈ LiZhongQC.integrableAutomorphicQD Γ F ∧
        ∀ μ : GammaMeasurableBeltrami.Space Γ,
          Integrable (fun ζ : ℂ =>
            GammaMeasurableBeltrami.planeRepresentative μ.val ζ * Θ ζ) (volume.restrict F) ∧
          (∫ ζ in LiZhongQC.upperHalf,
            GammaMeasurableBeltrami.planeRepresentative μ.val ζ * f ζ) =
            -LiZhongQC.beltramiPairing F
              (GammaMeasurableBeltrami.planeRepresentative μ.val) Θ := by
  let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
  let m : Γ → ℂ → ℂ := fun γ =>
    LiZhongQC.mobiusFn (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1)
  let mult := Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1))
  dsimp only
  intro ρ hρ
  let Θ : ℂ → ℂ := fun z => ∑' u : C, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2
  let A : Γ := ⟨A0, hA0⟩
  let e := rightCosetPowerEquiv Γ A s hs hproj ρ hρ
  have hm : (mult : ℂ) ≠ 0 := by
    exact_mod_cast (LiZhongQC.h36p_mult_pos (Γ := Γ)).ne'
  have hpoint (z : ℂ) (hz : z ∈ LiZhongQC.upperHalf) :
      HasSum (fun u : C => (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
        (-ProjectivePoincare.series Γ (lengthSeed s) z) := by
    have hnorm := ProjectivePoincare.summable_norm Γ hΓ
      (lengthSeed_differentiableOn s) (lengthSeed_area s) hz
    have hfull : HasSum (fun p : C × ℤ => ProjectivePoincare.term Γ (lengthSeed s) (e p) z)
        (ProjectivePoincare.series Γ (lengthSeed s) z) :=
      e.hasSum_iff.mpr hnorm.of_norm.hasSum
    have hfiber (u : C) :
        HasSum (fun n : ℤ => ProjectivePoincare.term Γ (lengthSeed s) (e (u, n)) z)
          (-((deriv (m (ρ u)) z / m (ρ u) z) ^ 2)) := by
      change HasSum (fun n : ℤ => ProjectivePoincare.term Γ (lengthSeed s)
        ((ProjectivePoincare.imageHom Γ A) ^ n * ProjectivePoincare.imageHom Γ (ρ u)) z) _
      have h := (lengthKernel_cyclic_hasSum Γ hΓ A0 hA0 s hs hproj
        (ProjectivePoincare.imageHom Γ (ρ u)) z hz).1
      rw [image_squaredLogDeriv Γ (ρ u) hz] at h
      exact h
    have h := (hfull.prod_fiberwise hfiber).neg
    simpa only [neg_neg] using h
  have hmatrix (z : ℂ) (hz : z ∈ LiZhongQC.upperHalf) :
      LiZhongQC.h36p_theta Γ (lengthSeed s) z = -(mult : ℂ) * Θ z := by
    have h := (hpoint z hz).tsum_eq
    change Θ z = -ProjectivePoincare.series Γ (lengthSeed s) z at h
    have he : ProjectivePoincare.series Γ (lengthSeed s) z = -Θ z := by
      rw [h, neg_neg]
    rw [ProjectivePoincare.matrix_sum_eq_card_mul Γ hΓ
      (lengthSeed_differentiableOn s) (lengthSeed_area s) hz, he]
    ring
  refine ⟨fun z hz => ⟨hpoint z hz, (hpoint z hz).summable.norm, hmatrix z hz⟩, ?_⟩
  intro F hF
  obtain ⟨hmatA, hunfold⟩ := LiZhongQC.h36p_poincare hΓ hF
    (lengthSeed_differentiableOn s) (lengthSeed_area s)
  have hscaled := LiZhongQC.h36p_b_A_smul hmatA (-(mult : ℂ)⁻¹)
  have heq (z : ℂ) (hz : z ∈ LiZhongQC.upperHalf) :
      Θ z = (-(mult : ℂ)⁻¹ • LiZhongQC.h36p_theta Γ (lengthSeed s)) z := by
    rw [Pi.smul_apply, smul_eq_mul, hmatrix z hz]
    field_simp [hm]
  have hThetaA : Θ ∈ LiZhongQC.integrableAutomorphicQD Γ F := by
    refine ⟨hscaled.1.congr heq, ?_, ?_⟩
    · have harea : LiZhongQC.phiArea Θ F =
          LiZhongQC.phiArea (-(mult : ℂ)⁻¹ • LiZhongQC.h36p_theta Γ (lengthSeed s)) F := by
        unfold LiZhongQC.phiArea
        apply setLIntegral_congr_fun hF.2.1
        intro z hz
        exact congrArg (fun w : ℂ => ENNReal.ofReal ‖w‖) (heq z (hF.1 hz))
      rw [harea]
      exact hscaled.2.1
    · intro γ hγ z hz
      change Θ (LiZhongQC.h36p_m γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = Θ z
      rw [heq z hz, heq (LiZhongQC.h36p_m γ z) (LiZhongQC.h36p_m_mem γ hz)]
      exact hscaled.2.2 γ hγ z hz
  refine ⟨hThetaA, ?_⟩
  intro μ
  let κ := GammaMeasurableBeltrami.planeRepresentative μ.val
  have hκ := GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff μ.val
  have hκΓ := GammaMeasurableBeltrami.planeRepresentative_isGammaCompatible μ
  have hint : Integrable (fun z => κ z * Θ z) (volume.restrict F) :=
    (LiZhongQC.h36p_integrableOn_A hF.1 hF.2.1 hThetaA).bdd_mul
      (hκ.1.mono_measure (Measure.restrict_mono hF.1 le_rfl))
      (ae_restrict_of_ae_restrict_of_subset hF.1 hκ.2)
  refine ⟨hint, ?_⟩
  have hmul : (mult : ℂ) * (∫ z in LiZhongQC.upperHalf, κ z * lengthSeed s z) =
      (mult : ℂ) * (-LiZhongQC.beltramiPairing F κ Θ) := by
    calc
      _ = LiZhongQC.beltramiPairing F κ (LiZhongQC.h36p_theta Γ (lengthSeed s)) :=
        hunfold κ hκ.1 ⟨‖μ.val‖, hκ.2⟩ hκΓ
      _ = -(mult : ℂ) * LiZhongQC.beltramiPairing F κ Θ := by
        unfold LiZhongQC.beltramiPairing
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hF.2.1] with z hz
        rw [hmatrix z (hF.1 hz)]
        ring
      _ = (mult : ℂ) * (-LiZhongQC.beltramiPairing F κ Θ) := by ring
  exact (mul_left_cancel₀ hm) hmul

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
