module

public import LowDimensionalTopology.External.LiZhongQC.Ch02.S13_Representation
public import Mathlib.Tactic.Linarith

/-!
# Analytic and geometric quasiconformality on plane domains

The analytic predicate uses actual ACL regularity and the almost-everywhere
Wirtinger inequality. Its equivalence with geometric quasiconformality is proved,
rather than included among the predicate's hypotheses. Coordinate changes,
Lebesgue area and the complex dilatation use the same genuine plane maps.

The analytic proofs reused here are due to Wu Xiaobin, from the fixed source
recorded with its license and local adaptations in the external provenance
manifest. The source commit is 1c0d5473c020b66ed5106331a38a61536760b9b2.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Analytic K-quasiconformality: a genuine homeomorphism on an open domain,
ACL regularity, and the almost-everywhere distortion inequality. -/
def IsAnalyticallyKQuasiconformal (f : ℂ → ℂ) (D : Set ℂ) (K : ℝ) : Prop :=
  IsOpen D ∧ 1 ≤ K ∧ LiZhongQC.IsHomeomorphOnto f D (f '' D) ∧
    LiZhongQC.IsACL f D ∧
      ∀ᵐ z ∂(volume.restrict D),
        ‖LiZhongQC.dz f z‖ + ‖LiZhongQC.dzbar f z‖ ≤
          K * (‖LiZhongQC.dz f z‖ - ‖LiZhongQC.dzbar f z‖)

/-- The K-form and the strict Beltrami-ratio form of the derivative inequality
have exactly the same normalization. -/
theorem wirtinger_inequality_iff {a b K : ℝ} (hK : 1 ≤ K) :
    a + b ≤ K * (a - b) ↔ b ≤ (K - 1) / (K + 1) * a := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : 0 < K + 1)]
  constructor <;> intro h <;> nlinarith

/-- The analytic and geometric conditions are equivalent, with the same K. -/
theorem geometric_iff_analytic {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} :
    LiZhongQC.IsKQC f D K ↔ IsAnalyticallyKQuasiconformal f D K := by
  constructor
  · intro hf
    exact ⟨hf.1, hf.2.1, hf.2.2.1,
      (LiZhongQC.thm10_1_isKQC_iff hf.1 hf.2.1 hf.2.2.1).mp hf⟩
  · rintro ⟨hD, hK, hhomeo, hacl, hbound⟩
    exact (LiZhongQC.thm10_1_isKQC_iff hD hK hhomeo).mpr ⟨hacl, hbound⟩

/-- A planar homeomorphism with both real partial derivatives almost everywhere
has a total real derivative almost everywhere. -/
theorem differentiable_ae_of_partials {f : ℂ → ℂ} {D E : Set ℂ} (hD : IsOpen D)
    (hf : LiZhongQC.IsHomeomorphOnto f D E)
    (hpart : ∀ᵐ z ∂(volume.restrict D),
      DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
        DifferentiableAt ℝ (fun t : ℝ => f (z + t * Complex.I)) 0) :
    ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ f z :=
  LiZhongQC.menchoff_M5 hD hf hpart

/-- Unit quasiconformal distortion is equivalent to a conformal domain map. -/
theorem one_quasiconformal_iff_conformal {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) :
    LiZhongQC.IsKQC f D 1 ↔ LiZhongQC.IsConformalOnto f D (f '' D) :=
  ⟨LiZhongQC.thm7_3_one_qc_conformal, LiZhongQC.isKQC_one_of_conformal hD⟩

/-- The geometric modulus bound implies actual absolute continuity on lines. -/
theorem geometric_quasiconformal_isACL {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K) : LiZhongQC.IsACL f D :=
  LiZhongQC.thm9_1_isACL hf

/-- The geometric modulus bound implies the analytic derivative inequality. -/
theorem geometric_quasiconformal_derivative_inequality
    {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : LiZhongQC.IsKQC f D K) :
    ∀ᵐ z ∂(volume.restrict D),
      ‖LiZhongQC.dz f z‖ + ‖LiZhongQC.dzbar f z‖ ≤
        K * (‖LiZhongQC.dz f z‖ - ‖LiZhongQC.dzbar f z‖) :=
  LiZhongQC.thm9_4_dilatation_ae hf

/-- Quasiconformal plane maps have an actual total real derivative almost everywhere. -/
theorem quasiconformal_differentiable_ae {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K) :
    ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ f z :=
  LiZhongQC.thm9_3_differentiable_ae hf

/-- Inversion preserves the same quasiconformal distortion bound. -/
theorem quasiconformal_inverse {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K) :
    LiZhongQC.IsKQC (Function.invFunOn f D) (f '' D) K :=
  LiZhongQC.thm7_2_inv hf

/-- Composition multiplies quasiconformal distortion bounds. -/
theorem quasiconformal_comp {f g : ℂ → ℂ} {D E : Set ℂ} {K L : ℝ}
    (hf : LiZhongQC.IsKQC f D K) (hg : LiZhongQC.IsKQC g E L)
    (himage : f '' D ⊆ E) : LiZhongQC.IsKQC (g ∘ f) D (K * L) :=
  LiZhongQC.thm7_1_comp hf hg himage

/-- Conformal precomposition preserves K exactly. -/
theorem quasiconformal_conformal_precompose {f h : ℂ → ℂ} {D U : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K) (hU : IsOpen U)
    (hh : LiZhongQC.IsConformalOnto h U D) : LiZhongQC.IsKQC (f ∘ h) U K := by
  have himage : h '' U ⊆ D := fun _ hz => hh.2.2 ▸ hz
  simpa only [one_mul] using
    LiZhongQC.thm7_1_comp (LiZhongQC.isKQC_one_of_conformal hU hh) hf himage

/-- Conformal postcomposition preserves K exactly. -/
theorem quasiconformal_conformal_postcompose {f h : ℂ → ℂ} {D V : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K)
    (hh : LiZhongQC.IsConformalOnto h (f '' D) V) : LiZhongQC.IsKQC (h ∘ f) D K := by
  simpa only [mul_one] using LiZhongQC.thm7_1_comp hf
    (LiZhongQC.isKQC_one_of_conformal (LiZhongQC.isOpen_image_of_isKQC hf) hh) subset_rfl

/-- Quasiconformality is unchanged by conformal coordinates on both domains. -/
theorem quasiconformal_conformal_coordinates {f h k : ℂ → ℂ} {D U V : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K) (hU : IsOpen U)
    (hh : LiZhongQC.IsConformalOnto h U D)
    (hk : LiZhongQC.IsConformalOnto k (f '' D) V) :
    LiZhongQC.IsKQC ((k ∘ f) ∘ h) U K :=
  quasiconformal_conformal_precompose (quasiconformal_conformal_postcompose hf hk) hU hh

/-- The Jacobian integral is precisely the Lebesgue area of every measurable image. -/
theorem quasiconformal_area_formula {f : ℂ → ℂ} {D E : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K) (hE : MeasurableSet E) (hED : E ⊆ D) :
    volume (f '' E) = ∫⁻ z in E, ENNReal.ofReal (LiZhongQC.jacobian f z) :=
  LiZhongQC.thm9_6_absolutelyContinuous hf hE hED

/-- The holomorphic Wirtinger derivative is nonzero almost everywhere. -/
theorem quasiconformal_dz_ne_zero_ae {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K) :
    ∀ᵐ z ∂(volume.restrict D), LiZhongQC.dz f z ≠ 0 := by
  filter_upwards [LiZhongQC.thm9_6_cor2_jacobian_pos hf] with z hz
  intro hzero
  rw [LiZhongQC.jacobian, hzero, norm_zero] at hz
  nlinarith [sq_nonneg ‖LiZhongQC.dzbar f z‖]

/-- The exact complex phase, not just its norm, occurs in the relative-map formula. -/
theorem complex_dilatation_comp_inverse {f g : ℂ → ℂ} {D : Set ℂ} {K L : ℝ}
    (hf : LiZhongQC.IsKQC f D K) (hg : LiZhongQC.IsKQC g D L) :
    ∀ᵐ z ∂(volume.restrict D),
      LiZhongQC.complexDilatation (f ∘ Function.invFunOn g D) (g z) =
        (LiZhongQC.complexDilatation f z - LiZhongQC.complexDilatation g z) /
            (1 - conj (LiZhongQC.complexDilatation g z) * LiZhongQC.complexDilatation f z) *
          (LiZhongQC.dz g z / conj (LiZhongQC.dz g z)) :=
  LiZhongQC.ahQ_comp_inv_dilatation hf hg

/-- The inverse complex dilatation formula follows from the same relative-map law. -/
theorem complex_dilatation_inverse {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K) :
    ∀ᵐ z ∂(volume.restrict D),
      LiZhongQC.complexDilatation (Function.invFunOn f D) (f z) =
        -LiZhongQC.complexDilatation f z *
          (LiZhongQC.dz f z / conj (LiZhongQC.dz f z)) := by
  have hid : LiZhongQC.IsKQC (id : ℂ → ℂ) D 1 :=
    LiZhongQC.isKQC_one_of_conformal hf.1
      ⟨differentiableOn_id, Set.injOn_id D, Set.image_id D⟩
  simpa only [Function.id_comp, LiZhongQC.nxT_complexDilatation_id,
    zero_sub, mul_zero, sub_zero, div_one] using
    LiZhongQC.ahQ_comp_inv_dilatation hid hf

end LowDimensionalTopology.Geometry.Quasiconformal
