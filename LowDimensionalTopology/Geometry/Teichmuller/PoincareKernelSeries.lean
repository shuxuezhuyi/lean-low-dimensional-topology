module

public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalReconstruction
public import LowDimensionalTopology.Geometry.Teichmuller.HalfPlaneQuadraticReproduction
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Poincare series on the entire actual projective source group

The summands use the actual Mobius action and its squared complex derivative.
The full special-linear family counts each transformation by its true finite
ineffective kernel. Local summable bounds give uniform convergence on compacta.
The immediate kernel consumer retains every differential on the original closed
surface and the literal unscaled fundamental-domain seed.

The analytic inputs are from Wu Xiaobin's Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0),
`S36_Hamilton.lean`. The explicit kernel unfolding below adapts that source.
See `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal UpperHalfPlane OnePoint Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.ProjectivePoincare

open LiZhongQC Hyperbolic Mobius

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))

/-- The original matrix group maps onto its exact entire Mobius image. -/
def imageHom : Γ →* Γ.map realSLMobius where
  toFun A := ⟨realSLMobius A.val, Subgroup.mem_map.mpr ⟨A.val, A.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one realSLMobius)
  map_mul' A B := Subtype.ext (map_mul realSLMobius A.val B.val)

/-- No special-linear homomorphic section is required to cover the actual image. -/
theorem imageHom_surjective : Function.Surjective (imageHom Γ) := by
  intro g
  obtain ⟨A, hA, he⟩ := Subgroup.mem_map.mp g.property
  exact ⟨⟨A, hA⟩, Subtype.ext he⟩

/-- The finite coordinate of the actual compactified action. Its value at an
infinite image is set to zero; every half-plane image is genuinely finite. -/
def action (g : Γ.map realSLMobius) (z : ℂ) : ℂ :=
  ((g.val.val (z : ExtendedComplex)).elim 0 id : ℂ)

/-- Every matrix representative gives the same actual action on the half-plane. -/
theorem action_image (A : Γ) {z : ℂ} (hz : z ∈ upperHalf) :
    action Γ (imageHom Γ A) z = h36p_m A.val z := by
  change ((realSLMobius A.val).val (z : ExtendedComplex)).elim 0 id = _
  rw [realSLMobius_action A.val (⟨z, hz⟩ : ℍ)]
  simpa only [OnePoint.elim_some, id_eq] using
    (h36p_m_coe A.val (⟨z, hz⟩ : ℍ)).symm

/-- The derivative is that of the actual action, not an additional chosen field. -/
theorem action_hasDerivAt_image (A : Γ) {z : ℂ} (hz : z ∈ upperHalf) :
    HasDerivAt (action Γ (imageHom Γ A))
      (1 / ((A.val 1 0 : ℂ) * z + A.val 1 1) ^ 2) z := by
  apply (h36p_m_hasDerivAt A.val hz).congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalf.mem_nhds hz] with w hw
  exact action_image Γ A hw

/-- The whole actual image preserves the half-plane. -/
theorem action_mem (g : Γ.map realSLMobius) {z : ℂ} (hz : z ∈ upperHalf) :
    action Γ g z ∈ upperHalf := by
  obtain ⟨A, rfl⟩ := imageHom_surjective Γ g
  rw [action_image Γ A hz]
  exact h36p_m_mem A.val hz

/-- The genuine quadratic pullback summand for an actual transformation. -/
def term (f : ℂ → ℂ) (g : Γ.map realSLMobius) (z : ℂ) : ℂ :=
  f (action Γ g z) * (deriv (action Γ g) z) ^ 2

/-- The squared derivative agrees with the literal weight-four matrix formula
for every representative of the same actual transformation. -/
theorem term_image (f : ℂ → ℂ) (A : Γ) {z : ℂ} (hz : z ∈ upperHalf) :
    term Γ f (imageHom Γ A) z =
      f (h36p_m A.val z) / ((A.val 1 0 : ℂ) * z + A.val 1 1) ^ 4 := by
  unfold term
  rw [action_image Γ A hz, (action_hasDerivAt_image Γ A hz).deriv]
  simp only [div_pow, one_pow, ← pow_mul, mul_one_div]

/-- The Poincare series is indexed by every actual transformation exactly once. -/
def series (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' g : Γ.map realSLMobius, term Γ f g z

private def kernelEquiv : (imageHom Γ).ker ≃ ↥(Γ ⊓ Subgroup.zpowers (-1)) where
  toFun A := by
    have he : realSLMobius A.val.val = 1 :=
      congrArg Subtype.val (show imageHom Γ A.val = 1 from A.property)
    have hs : realSLMobius 1 = realSLMobius A.val.val :=
      (map_one realSLMobius).trans he.symm
    have hm : A.val.val ∈ Subgroup.zpowers (-1) := by
      rcases (realSLMobius_eq_iff_sign 1 A.val.val).mp hs with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        exact Subgroup.mem_zpowers _
    exact ⟨A.val.val, A.val.property, hm⟩
  invFun A := by
    refine ⟨⟨A.val, A.property.1⟩, ?_⟩
    change imageHom Γ ⟨A.val, A.property.1⟩ = 1
    apply Subtype.ext
    change realSLMobius A.val = 1
    rcases h36p_a_mem_zpowers A.property.2 with h | h
    · rw [h, map_one]
    · rw [h, realSLMobius_neg, map_one]
  left_inv _ := rfl
  right_inv _ := rfl

/-- Each actual transformation has the exact original ineffective multiplicity. -/
theorem fiber_card (g : Γ.map realSLMobius) :
    Nat.card ((imageHom Γ) ⁻¹' {g}) = Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) := by
  exact (Nat.card_congr
    (MonoidHom.fiberEquivKerOfSurjective (imageHom_surjective Γ) g)).trans
    (Nat.card_congr (kernelEquiv Γ))

private theorem matrix_compact_majorant (hΓ : IsFuchsian Γ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalf) (hfA : phiArea f upperHalf < ⊤)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ upperHalf) :
    ∃ u : Γ → ℝ, Summable u ∧ ∀ A : Γ, ∀ z ∈ K,
      ‖f (h36p_m A.val z) / ((A.val 1 0 : ℂ) * z + A.val 1 1) ^ 4‖ ≤ u A := by
  classical
  have hlocal : ∀ z : K, ∃ u : Γ → ℝ, Summable u ∧ ∀ A : Γ,
      ∀ w ∈ ball z.val (z.val.im / 4),
        ‖f (h36p_m A.val w) / ((A.val 1 0 : ℂ) * w + A.val 1 1) ^ 4‖ ≤ u A :=
    fun z => h36p_b_local hΓ hf hfA (hKH z.property)
  choose u hu hle using hlocal
  have hu0 (z : K) (A : Γ) : 0 ≤ u z A :=
    (norm_nonneg _).trans (hle z A z.val (mem_ball_self (by
      exact div_pos (hKH z.property) (by norm_num))))
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun z : K => ball z.val (z.val.im / 4)) (fun _ => isOpen_ball)
    (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (by
      exact div_pos (hKH hz) (by norm_num))⟩)
  refine ⟨fun A => ∑ z ∈ s, u z A, summable_sum (fun z _ => hu z), ?_⟩
  intro A z hz
  obtain ⟨w, hws, hzw⟩ := mem_iUnion₂.mp (hs hz)
  exact (hle w A z hzw).trans (Finset.single_le_sum (fun v _ => hu0 v A) hws)

/-- A true summable majorant controls every actual-image term on any compact
half-plane subset, including the empty compact set. -/
theorem compact_majorant (hΓ : IsFuchsian Γ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalf) (hfA : phiArea f upperHalf < ⊤)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ upperHalf) :
    ∃ u : Γ.map realSLMobius → ℝ, Summable u ∧
      ∀ g : Γ.map realSLMobius, ∀ z ∈ K, ‖term Γ f g z‖ ≤ u g := by
  classical
  obtain ⟨u, hu, hle⟩ := matrix_compact_majorant Γ hΓ hf hfA hK hKH
  let σ : Γ.map realSLMobius → Γ := fun g => (imageHom_surjective Γ g).choose
  have hσ (g : Γ.map realSLMobius) : imageHom Γ (σ g) = g :=
    (imageHom_surjective Γ g).choose_spec
  have hσi : Function.Injective σ := by
    intro g h he
    calc
      g = imageHom Γ (σ g) := (hσ g).symm
      _ = imageHom Γ (σ h) := congrArg (imageHom Γ) he
      _ = h := hσ h
  refine ⟨u ∘ σ, hu.comp_injective hσi, ?_⟩
  intro g z hz
  have ht := term_image Γ f (σ g) (hKH hz)
  rw [hσ g] at ht
  rw [ht]
  exact hle (σ g) z hz

/-- Absolute convergence holds at every original half-plane point. -/
theorem summable_norm (hΓ : IsFuchsian Γ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalf) (hfA : phiArea f upperHalf < ⊤)
    {z : ℂ} (hz : z ∈ upperHalf) :
    Summable (fun g : Γ.map realSLMobius => ‖term Γ f g z‖) := by
  obtain ⟨u, hu, hle⟩ := compact_majorant Γ hΓ hf hfA
    isCompact_singleton (singleton_subset_iff.mpr hz)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun g => hle g z (mem_singleton z)) hu

/-- The actual full-image series converges uniformly on every compact subset. -/
theorem tendstoUniformlyOn (hΓ : IsFuchsian Γ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalf) (hfA : phiArea f upperHalf < ⊤)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ upperHalf) :
    TendstoUniformlyOn
      (fun s : Finset (Γ.map realSLMobius) => fun z => ∑ g ∈ s, term Γ f g z)
      (series Γ f) atTop K := by
  obtain ⟨u, hu, hle⟩ := compact_majorant Γ hΓ hf hfA hK hKH
  exact tendstoUniformlyOn_tsum hu hle

private theorem fiber_term_sum (f : ℂ → ℂ) (g : Γ.map realSLMobius)
    {z : ℂ} (hz : z ∈ upperHalf) :
    (∑' A : (imageHom Γ) ⁻¹' {g},
      f (h36p_m A.val.val z) / ((A.val.val 1 0 : ℂ) * z + A.val.val 1 1) ^ 4) =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) * term Γ f g z := by
  classical
  let : Finite ((imageHom Γ) ⁻¹' {g}) := Nat.finite_of_card_ne_zero (by
    rw [fiber_card Γ g]
    exact (h36p_mult_pos (Γ := Γ)).ne')
  let : Fintype ((imageHom Γ) ⁻¹' {g}) := Fintype.ofFinite _
  rw [tsum_fintype]
  calc
    _ = ∑ _A : (imageHom Γ) ⁻¹' {g}, term Γ f g z := by
      apply Finset.sum_congr rfl
      intro A _
      have ht := term_image Γ f A.val hz
      rw [show imageHom Γ A.val = g from A.property] at ht
      exact ht.symm
    _ = (Nat.card ((imageHom Γ) ⁻¹' {g}) : ℂ) * term Γ f g z := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    _ = _ := by rw [fiber_card Γ g]

/-- The entire matrix family counts the true actual-image series with exactly
its original ineffective multiplicity, including both signs when present. -/
theorem matrix_sum_eq_card_mul (hΓ : IsFuchsian Γ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalf) (hfA : phiArea f upperHalf < ⊤)
    {z : ℂ} (hz : z ∈ upperHalf) :
    h36p_theta Γ f z = (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) * series Γ f z := by
  obtain ⟨u, hu, hle⟩ := h36p_b_local hΓ hf hfA hz
  have hr : Summable (fun A : Γ =>
      ‖f (h36p_m A.val z) / ((A.val 1 0 : ℂ) * z + A.val 1 1) ^ 4‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun A => hle A z (mem_ball_self (by exact div_pos hz (by norm_num)))) hu
  have hgroup := hr.of_norm.hasSum.tsum_fiberwise (imageHom Γ)
  change (∑' A : Γ, f (h36p_m A.val z) /
    ((A.val 1 0 : ℂ) * z + A.val 1 1) ^ 4) = _
  calc
    _ = ∑' g : Γ.map realSLMobius, ∑' A : (imageHom Γ) ⁻¹' {g},
        f (h36p_m A.val.val z) / ((A.val.val 1 0 : ℂ) * z + A.val.val 1 1) ^ 4 :=
      hgroup.tsum_eq.symm
    _ = ∑' g : Γ.map realSLMobius,
        (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) * term Γ f g z :=
      tsum_congr (fun g => fiber_term_sum Γ f g hz)
    _ = _ := tsum_mul_left

/-- The actual projective sum is the explicitly normalized original matrix sum. -/
theorem series_eq_inv_mul_matrix (hΓ : IsFuchsian Γ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalf) (hfA : phiArea f upperHalf < ⊤)
    {z : ℂ} (hz : z ∈ upperHalf) :
    series Γ f z = (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ)⁻¹ * h36p_theta Γ f z := by
  have hm : (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) ≠ 0 := by
    exact_mod_cast (h36p_mult_pos (Γ := Γ)).ne'
  rw [matrix_sum_eq_card_mul Γ hΓ hf hfA hz]
  simp only [← mul_assoc, inv_mul_cancel₀ hm, one_mul]

/-- Holomorphy is derived for the same full-image series. -/
theorem differentiableOn (hΓ : IsFuchsian Γ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalf) (hfA : phiArea f upperHalf < ⊤) :
    DifferentiableOn ℂ (series Γ f) upperHalf := by
  apply ((h36p_b_theta_diff hΓ hf hfA).const_mul
    (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ)⁻¹).congr
  intro z hz
  exact series_eq_inv_mul_matrix Γ hΓ hf hfA hz

/-- Every actual source transformation satisfies the original quadratic
pullback equation for the same whole-image series. -/
theorem automorphic (hΓ : IsFuchsian Γ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalf) (hfA : phiArea f upperHalf < ⊤)
    (g : Γ.map realSLMobius) {z : ℂ} (hz : z ∈ upperHalf) :
    series Γ f (action Γ g z) * (deriv (action Γ g) z) ^ 2 = series Γ f z := by
  change term Γ (series Γ f) g z = _
  obtain ⟨A, rfl⟩ := imageHom_surjective Γ g
  rw [term_image Γ (series Γ f) A hz]
  rw [series_eq_inv_mul_matrix Γ hΓ hf hfA (h36p_m_mem A.val hz),
    series_eq_inv_mul_matrix Γ hΓ hf hfA hz]
  rw [mul_div_assoc]
  congr 1
  exact h36p_b_automorphic f A.val A.property z hz

end LowDimensionalTopology.Geometry.Teichmuller.ProjectivePoincare

namespace LowDimensionalTopology.Geometry.Teichmuller.AutomorphicPoincare

open Surfaces LiZhongQC QuadraticBergman ProjectivePoincare Hyperbolic

/-- The specified fundamental-domain seed, with no ineffective-kernel scaling. -/
def seed (F : Set ℂ) (φ : ℂ → ℂ) (w : ℂ) : ℂ :=
  (12 / Real.pi : ℂ) * ∫ ζ in F, h36p_c_K φ ζ w

/-- This is the literal kernel integral with the original conjugate-first slot. -/
theorem seed_eq_kernel (F : Set ℂ) (φ : ℂ → ℂ) (w : ℂ) :
    seed F φ w = ∫ ζ in F, (ζ.im : ℂ) ^ 2 * φ ζ *
      conj (halfPlaneQuadraticKernel w ζ) := by
  have heq : (fun ζ : ℂ => (ζ.im : ℂ) ^ 2 * φ ζ * conj (halfPlaneQuadraticKernel w ζ)) =
      fun ζ => (12 / Real.pi : ℂ) * h36p_c_K φ ζ w := by
    funext ζ
    have hpow : (w - conj ζ) ^ 4 = (conj ζ - w) ^ 4 := by ring
    simp only [halfPlaneQuadraticKernel, map_div₀, map_ofNat, Complex.conj_ofReal,
      map_pow, map_sub, Complex.conj_conj]
    rw [hpow]
    unfold h36p_c_K
    ring
  rw [heq, integral_const_mul]
  rfl

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hΓ : IsFuchsian Γ)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)

include hΓ hp hF

/-- The genuine seed is holomorphic without an added regularity premise. -/
theorem seed_differentiableOn (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    DifferentiableOn ℂ (seed F (uniformizedQuadratic R p q)) upperHalf := by
  have hφ := uniformizedQuadratic_integrableAutomorphic R p hΓ hp hF q
  exact (h36p_c_beta_diff hF.2.1 hF.1 hφ.1.continuousOn hφ.2.1).const_mul _

/-- The unweighted full-half-plane L1 condition is proved for the actual seed. -/
theorem seed_phiArea_lt_top (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    phiArea (seed F (uniformizedQuadratic R p q)) upperHalf < ⊤ := by
  have hφ := uniformizedQuadratic_integrableAutomorphic R p hΓ hp hF q
  have hb := h36p_c_beta_L1 hF.2.1 hF.1 hφ.1.continuousOn hφ.2.1
  unfold seed phiArea
  calc
    ∫⁻ w in upperHalf,
        ENNReal.ofReal ‖(12 / Real.pi : ℂ) * ∫ ζ in F, h36p_c_K (uniformizedQuadratic R p q) ζ w‖ =
      ENNReal.ofReal ‖(12 / Real.pi : ℂ)‖ *
        ∫⁻ w in upperHalf, ENNReal.ofReal ‖∫ ζ in F, h36p_c_K (uniformizedQuadratic R p q) ζ w‖ := by
      simp_rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb

/-- The entire original matrix group counts the literal seed with its true
ineffective multiplicity; no sign is removed from the source group. -/
theorem seed_matrix_sum (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {z : ℂ} (hz : z ∈ upperHalf) :
    h36p_theta Γ (seed F (uniformizedQuadratic R p q)) z =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) * uniformizedQuadratic R p q z := by
  let φ := uniformizedQuadratic R p q
  have hφ : φ ∈ integrableAutomorphicQD Γ F :=
    uniformizedQuadratic_integrableAutomorphic R p hΓ hp hF q
  have hGi := h36p_c_Gz_int hΓ hF hφ hz
  have hU := h36p_c_unfold_int hΓ hF hGi
  have hR := h36p_c_rp_upper hφ.1 hz hGi
  let c : ℂ := 12 / Real.pi
  have hterm : ∀ A : Γ,
      c * (∫ ζ in F, h36p_c_K φ ζ (h36p_m A.val z)) /
        ((A.val 1 0 : ℂ) * z + A.val 1 1) ^ 4 =
      c * ∫ ζ in F, h36p_c_K φ ζ (h36p_m A.val z) /
        ((A.val 1 0 : ℂ) * z + A.val 1 1) ^ 4 := by
    intro A
    rw [mul_div_assoc, integral_div]
  have hterm2 : ∀ A : Γ,
      c * ∫ ζ in F, h36p_c_K φ ζ (h36p_m A.val⁻¹ z) /
        (((A.val⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
          (A.val⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) ^ 4 =
      c * ∫ ζ in F, ((‖(A.val 1 0 : ℂ) * ζ + A.val 1 1‖⁻¹ ^ 4 : ℝ) : ℂ) *
        h36p_c_K φ (h36p_m A.val ζ) z := by
    intro A
    congr 1
    exact setIntegral_congr_fun hF.2.1 fun ζ hζ => h36p_c_kinv hφ A.property (hF.1 hζ) hz
  have hre := (Equiv.inv Γ).tsum_eq (fun A : Γ => c * ∫ ζ in F,
    h36p_c_K φ ζ (h36p_m A.val z) / ((A.val 1 0 : ℂ) * z + A.val 1 1) ^ 4)
  change (∑' A : Γ, c * (∫ ζ in F, h36p_c_K φ ζ (h36p_m A.val z)) /
    ((A.val 1 0 : ℂ) * z + A.val 1 1) ^ 4) = _
  rw [tsum_congr hterm, ← hre]
  change (∑' A : Γ, c * ∫ ζ in F, h36p_c_K φ ζ (h36p_m A.val⁻¹ z) /
    (((A.val⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
      (A.val⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) ^ 4) = _
  rw [tsum_congr hterm2, tsum_mul_left, hU, hR]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hc : c * (Real.pi / 12 : ℂ) = 1 := by
    dsimp only [c]
    field_simp
  calc
    c * ((Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) * ((Real.pi / 12 : ℂ) * φ z)) =
      (c * (Real.pi / 12 : ℂ)) * ((Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) * φ z) := by ring
    _ = _ := by rw [hc, one_mul]

/-- Every original coefficient is the actual whole-image Poincare series of
the specified unscaled seed, at every original half-plane point. -/
theorem uniformizedQuadratic_eq_series
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) {z : ℂ} (hz : z ∈ upperHalf) :
    uniformizedQuadratic R p q z =
      series Γ (seed F (uniformizedQuadratic R p q)) z := by
  have hm : (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) ≠ 0 := by
    exact_mod_cast (h36p_mult_pos (Γ := Γ)).ne'
  have he := seed_matrix_sum R p hΓ hp hF q hz
  rw [matrix_sum_eq_card_mul Γ hΓ
    (seed_differentiableOn R p hΓ hp hF q) (seed_phiArea_lt_top R p hΓ hp hF q) hz] at he
  exact (mul_left_cancel₀ hm he).symm

/-- The original coefficient expansion is absolutely convergent at every point. -/
theorem uniformizedQuadratic_series_summable_norm
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) {z : ℂ} (hz : z ∈ upperHalf) :
    Summable (fun g : Γ.map realSLMobius =>
      ‖term Γ (seed F (uniformizedQuadratic R p q)) g z‖) :=
  summable_norm Γ hΓ (seed_differentiableOn R p hΓ hp hF q)
    (seed_phiArea_lt_top R p hΓ hp hF q) hz

/-- The same full-image expansion converges uniformly on every compact subset. -/
theorem uniformizedQuadratic_series_tendstoUniformlyOn
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ upperHalf) :
    TendstoUniformlyOn
      (fun s : Finset (Γ.map realSLMobius) => fun z =>
        ∑ g ∈ s, term Γ (seed F (uniformizedQuadratic R p q)) g z)
      (uniformizedQuadratic R p q) atTop K := by
  apply (ProjectivePoincare.tendstoUniformlyOn Γ hΓ (seed_differentiableOn R p hΓ hp hF q)
    (seed_phiArea_lt_top R p hΓ hp hF q) hK hKH).congr_right
  intro z hz
  exact (uniformizedQuadratic_eq_series R p hΓ hp hF q (hKH hz)).symm

/-- The full original holomorphic automorphic space has the same explicit
kernel expansion; no extra integral or weighted-L2 membership is assumed. -/
theorem automorphic_kernel_series (φ : ℂ → ℂ)
    (hφ : DifferentiableOn ℂ φ upperHalf)
    (hφΓ : ∀ A ∈ Γ, ∀ z ∈ upperHalf,
      φ (((A 0 0 : ℂ) * z + A 0 1) / ((A 1 0 : ℂ) * z + A 1 1)) /
        ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = φ z) :
    (∀ z ∈ upperHalf, φ z = series Γ (seed F φ) z ∧
      Summable (fun g : Γ.map realSLMobius => ‖term Γ (seed F φ) g z‖)) ∧
    ∀ K : Set ℂ, IsCompact K → K ⊆ upperHalf →
      TendstoUniformlyOn
        (fun s : Finset (Γ.map realSLMobius) => fun z => ∑ g ∈ s, term Γ (seed F φ) g z)
        φ atTop K := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨q, hq, hqφ⟩ := utm_x_descent hp hφ hφΓ
  let Q : HolomorphicQuadraticDifferential R.toRiemannAtlas := ⟨q, hq⟩
  have hQ (ζ : ℂ) (hζ : ζ ∈ upperHalf) : uniformizedQuadratic R p Q ζ = φ ζ :=
    hqφ ζ hζ
  have hseed : seed F (uniformizedQuadratic R p Q) = seed F φ := by
    funext w
    unfold seed
    congr 1
    exact setIntegral_congr_fun hF.2.1 fun ζ hζ => by
      unfold h36p_c_K
      rw [hQ ζ (hF.1 hζ)]
  rw [← hseed]
  refine ⟨?_, ?_⟩
  · intro z hz
    exact ⟨(hQ z hz).symm.trans (uniformizedQuadratic_eq_series R p hΓ hp hF Q hz),
      uniformizedQuadratic_series_summable_norm R p hΓ hp hF Q hz⟩
  · intro K hK hKH
    apply (uniformizedQuadratic_series_tendstoUniformlyOn R p hΓ hp hF Q hK hKH).congr_right
    intro z hz
    exact hQ z (hKH hz)

end LowDimensionalTopology.Geometry.Teichmuller.AutomorphicPoincare
