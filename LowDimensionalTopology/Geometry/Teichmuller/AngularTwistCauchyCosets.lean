module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchyPullback
public import LowDimensionalTopology.Geometry.Teichmuller.CoefficientRealMobiusIsometry
public import LowDimensionalTopology.Geometry.Teichmuller.NativeDeformedCoefficientNaturality
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalRegions
public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
public import Mathlib.GroupTheory.Coset.Basic

/-!
# Angular coefficients and integrals on actual right cosets

Left multiplication by a positive dilation preserves the elementary
coefficient and its actual normalized Cauchy integral. The central sign of
a special-linear lift also preserves them. Thus the coefficient descends
to right cosets of the inverse image of the genuine projective cyclic group.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The transported pointwise coefficient is unchanged by the central matrix sign. -/
theorem pullbackInfinitesimalZeroExtension_neg (θ : Width) (γ : Deck) :
    pullbackInfinitesimalZeroExtension θ (-γ) = pullbackInfinitesimalZeroExtension θ γ := by
  funext ζ
  by_cases hζ : 0 < ζ.im
  · let z : ℍ := ⟨ζ, hζ⟩
    change pullbackInfinitesimalZeroExtension θ (-γ) (z : ℂ) =
      pullbackInfinitesimalZeroExtension θ γ (z : ℂ)
    rw [pullbackInfinitesimalZeroExtension_coe, pullbackInfinitesimalZeroExtension_coe,
      LiZhongQC.s30l_neg_smul, NormalizedCoefficientTransport.phase_neg]
  · rw [pullbackInfinitesimalZeroExtension_eq_zero_of_im_nonpos θ (-γ) (le_of_not_gt hζ),
      pullbackInfinitesimalZeroExtension_eq_zero_of_im_nonpos θ γ (le_of_not_gt hζ)]

/-- The actual coefficient depends on the genuine Mobius map, independently of its lift. -/
theorem pullbackInfinitesimalZeroExtension_eq_of_realSLMobius_eq (θ : Width)
    {γ δ : Deck} (hγδ : Hyperbolic.realSLMobius γ = Hyperbolic.realSLMobius δ) :
    pullbackInfinitesimalZeroExtension θ γ = pullbackInfinitesimalZeroExtension θ δ := by
  rcases (Hyperbolic.realSLMobius_eq_iff_sign γ δ).mp hγδ with h | h
  · rw [h]
  · rw [h, pullbackInfinitesimalZeroExtension_neg]

private theorem phase_hLogDilationSL (s : ℝ) (z : ℍ) :
    GammaMeasurableBeltrami.phase (Fuchsian.hLogDilationSL s) z = 1 := by
  have hd : GammaMeasurableBeltrami.denominator (Fuchsian.hLogDilationSL s) z =
      (Real.exp (-s) : ℂ) := by
    simp [GammaMeasurableBeltrami.denominator, Fuchsian.hLogDilationSL]
  rw [GammaMeasurableBeltrami.phase, hd, map_pow, Complex.conj_ofReal]
  exact div_self (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (-s))))

private theorem hLogDilationSL_smul_eq_pos_real_smul (s : ℝ) (z : ℍ) :
    Fuchsian.hLogDilationSL s • z =
      (⟨Real.exp (2 * s), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) • z := by
  apply UpperHalfPlane.ext
  rw [Fuchsian.hLogDilationSL_coe, UpperHalfPlane.coe_pos_real_smul, Complex.real_smul]

/-- Left composition by any positive logarithmic dilation preserves the actual coefficient. -/
theorem pullbackInfinitesimalZeroExtension_hLogDilationSL_mul
    (θ : Width) (s : ℝ) (γ : Deck) :
    pullbackInfinitesimalZeroExtension θ (Fuchsian.hLogDilationSL s * γ) =
      pullbackInfinitesimalZeroExtension θ γ := by
  funext ζ
  by_cases hζ : 0 < ζ.im
  · let z : ℍ := ⟨ζ, hζ⟩
    change pullbackInfinitesimalZeroExtension θ (Fuchsian.hLogDilationSL s * γ) (z : ℂ) =
      pullbackInfinitesimalZeroExtension θ γ (z : ℂ)
    simp only [pullbackInfinitesimalZeroExtension_coe, mul_smul,
      GammaMeasurableBeltrami.phase_mul, phase_hLogDilationSL,
      hLogDilationSL_smul_eq_pos_real_smul, infinitesimal_pos_real_smul, one_mul]
  · rw [pullbackInfinitesimalZeroExtension_eq_zero_of_im_nonpos θ
        (Fuchsian.hLogDilationSL s * γ) (le_of_not_gt hζ),
      pullbackInfinitesimalZeroExtension_eq_zero_of_im_nonpos θ γ (le_of_not_gt hζ)]

/-- The same positive left composition preserves the actual normalized integral. -/
theorem pullbackCauchyTerm_hLogDilationSL_mul (θ : Width) (s : ℝ) (γ : Deck) :
    pullbackCauchyTerm θ (Fuchsian.hLogDilationSL s * γ) = pullbackCauchyTerm θ γ := by
  unfold pullbackCauchyTerm
  rw [pullbackInfinitesimalZeroExtension_hLogDilationSL_mul]

/-- Every matrix lifting a projective power of the dilation preserves the coefficient
under left composition, including either central sign of each power. -/
theorem pullbackInfinitesimalZeroExtension_projectiveDilation_mul
    (θ : Width) (s : ℝ) (h γ : Deck)
    (hh : Hyperbolic.realSLMobius h ∈
      Subgroup.zpowers (Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))) :
    pullbackInfinitesimalZeroExtension θ (h * γ) = pullbackInfinitesimalZeroExtension θ γ := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh
  have he : Hyperbolic.realSLMobius h =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL ((n : ℝ) * s)) := by
    rw [← Fuchsian.hLogDilationSL_zpow s n, map_zpow]
    exact hn.symm
  have hem : Hyperbolic.realSLMobius (h * γ) =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL ((n : ℝ) * s) * γ) := by
    simpa only [map_mul] using congrArg (fun f => f * Hyperbolic.realSLMobius γ) he
  exact (pullbackInfinitesimalZeroExtension_eq_of_realSLMobius_eq θ hem).trans
    (pullbackInfinitesimalZeroExtension_hLogDilationSL_mul θ _ γ)

/-- The subgroup of the actual matrix group lying over the genuine projective cyclic group. -/
def projectiveDilationSubgroup (Γ : Subgroup Deck) (s : ℝ) : Subgroup Γ :=
  (Subgroup.zpowers (Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))).comap
    (Hyperbolic.realSLMobius.comp Γ.subtype)

/-- Equal actual right cosets give the same coefficient at every point of the plane. -/
theorem pullbackInfinitesimalZeroExtension_rightRel (θ : Width)
    (Γ : Subgroup Deck) (s : ℝ) (γ δ : Γ)
    (hγδ : QuotientGroup.rightRel (projectiveDilationSubgroup Γ s) γ δ) :
    pullbackInfinitesimalZeroExtension θ γ.val =
      pullbackInfinitesimalZeroExtension θ δ.val := by
  have hmem : δ * γ⁻¹ ∈ projectiveDilationSubgroup Γ s :=
    QuotientGroup.rightRel_apply.mp hγδ
  have hp : Hyperbolic.realSLMobius (δ.val * γ.val⁻¹) ∈
      Subgroup.zpowers (Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s)) := by
    simpa only [projectiveDilationSubgroup, Subgroup.mem_comap, MonoidHom.comp_apply,
      Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv] using hmem
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using
    (pullbackInfinitesimalZeroExtension_projectiveDilation_mul θ s (δ.val * γ.val⁻¹) γ.val hp).symm

/-- Equal actual right cosets give the same normalized Cauchy integral at every point. -/
theorem pullbackCauchyTerm_rightRel (θ : Width) (Γ : Subgroup Deck) (s : ℝ) (γ δ : Γ)
    (hγδ : QuotientGroup.rightRel (projectiveDilationSubgroup Γ s) γ δ) :
    pullbackCauchyTerm θ γ.val = pullbackCauchyTerm θ δ.val := by
  unfold pullbackCauchyTerm
  rw [pullbackInfinitesimalZeroExtension_rightRel θ Γ s γ δ hγδ]

/-- The intrinsic zero-extended infinitesimal coefficient on actual right cosets. -/
def rightCosetInfinitesimalZeroExtension (θ : Width) (Γ : Subgroup Deck) (s : ℝ) :
    Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)) → ℂ → ℂ :=
  Quotient.lift (fun γ : Γ => pullbackInfinitesimalZeroExtension θ γ.val)
    (fun γ δ hγδ => pullbackInfinitesimalZeroExtension_rightRel θ Γ s γ δ hγδ)

/-- Evaluation at a representative is the original actual transported coefficient. -/
@[simp] theorem rightCosetInfinitesimalZeroExtension_mk
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ) (γ : Γ) :
    rightCosetInfinitesimalZeroExtension θ Γ s (Quotient.mk _ γ) =
      pullbackInfinitesimalZeroExtension θ γ.val := rfl

/-- Each intrinsic coset coefficient is measurable for actual planar area. -/
theorem measurable_rightCosetInfinitesimalZeroExtension (θ : Width) (Γ : Subgroup Deck)
    (s : ℝ) (q : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))) :
    Measurable (rightCosetInfinitesimalZeroExtension θ Γ s q) := by
  refine Quotient.inductionOn q ?_
  intro γ
  exact measurable_pullbackInfinitesimalZeroExtension θ γ.val

/-- Every intrinsic coset coefficient retains the original pointwise angular bound. -/
theorem norm_rightCosetInfinitesimalZeroExtension_le (θ : Width) (Γ : Subgroup Deck)
    (s : ℝ) (q : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))) (ζ : ℂ) :
    ‖rightCosetInfinitesimalZeroExtension θ Γ s q ζ‖ ≤ 1 / (4 * (θ : ℝ)) := by
  refine Quotient.inductionOn q ?_
  intro γ
  exact norm_pullbackInfinitesimalZeroExtension_le θ γ.val ζ

/-- The original three-pole integrand remains absolutely integrable for every actual coset. -/
theorem integrable_rightCosetInfinitesimalZeroExtension_mul_firstVariationKernel
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ)
    (q : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))) (z : ℂ) :
    Integrable (fun ζ : ℂ => rightCosetInfinitesimalZeroExtension θ Γ s q ζ *
      Quasiconformal.firstVariationKernel z ζ) (volume : Measure ℂ) := by
  refine Quotient.inductionOn q ?_
  intro γ
  exact integrable_pullbackInfinitesimalZeroExtension_mul_firstVariationKernel θ γ.val z

/-- The intrinsic coset term is the actual normalized Cauchy integral of its coefficient. -/
def rightCosetCauchyTerm (θ : Width) (Γ : Subgroup Deck) (s : ℝ)
    (q : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))) : ℂ → ℂ :=
  LiZhongQC.ahVar (rightCosetInfinitesimalZeroExtension θ Γ s q)

/-- Every representative gives the same original actual transported integral. -/
@[simp] theorem rightCosetCauchyTerm_mk (θ : Width) (Γ : Subgroup Deck) (s : ℝ) (γ : Γ) :
    rightCosetCauchyTerm θ Γ s (Quotient.mk _ γ) = pullbackCauchyTerm θ γ.val := rfl

/-- The identity coset contributes exactly the original first angular integral. -/
theorem rightCosetCauchyTerm_identity (θ : Width) (Γ : Subgroup Deck) (s : ℝ) :
    rightCosetCauchyTerm θ Γ s (Quotient.mk _ (1 : Γ)) = firstCauchyTerm θ := by
  rw [rightCosetCauchyTerm_mk]
  exact pullbackCauchyTerm_identity θ

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
