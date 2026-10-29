module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonKernelSquareBounds
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonInvariantTruncation
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonBilinearMobiusCovariance
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Original direction integrals and ordered invariant limits
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter Topology
open scoped UpperHalfPlane ComplexConjugate ENNReal Manifold ContDiff Pointwise

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth

private theorem native_bilinear_row_bound
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (u v : E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ : ℍ,
      MemLp (SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF v) ζ) 2 flatArea ∧
        (∫ z : ℍ, ‖SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF v) ζ z‖ ^ 2 ∂flatArea) ≤
          M * (ζ.im ^ 2)⁻¹ := by
  let := C
  let bu := TH ν P F hF hsmooth ((K (β ν.val)).symm u)
  let bv := TH ν P F hF hsmooth ((K (β ν.val)).symm v)
  let b : Ambient := bu.val.val
  let c : Ambient := bv.val.val
  rcases (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic
    (deformedNativeSurface R hgenus hΓ hp ν) P (deformedTargetCover R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) F hF bu.val).mp bu.property with ⟨q, hq⟩
  let M : ℝ := Real.pi ^ 2 * SourceKernel.squareRowMass ^ 2 * ‖c‖ ^ 2 * ‖b‖ ^ 2 * Real.pi / 4
  refine ⟨M, by dsimp only [M]; positivity, fun ζ => ?_⟩
  let f : ℍ → ℂ := fun η => SourceKernel.outerInput (fun ξ => c ξ) (fun ξ => b ξ) ζ η
  have hout := SourceKernel.outerQuadratic_row_square_bound
    (deformedNativeSurface R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) c q ζ
  rw [hq] at hout
  have hQ := SourceKernel.squareCrossIntegral_memLp_two f hout.1
  have he : SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF v) ζ =
      fun z : ℍ => -(Real.pi : ℂ) * SourceKernel.squareCrossIntegral f z := by
    funext z
    rw [nativeWeilPetersson_bilinear_transpose R hp hg hgenus hΓ hfree hsmooth ν P F hF u v ζ z]
    exact SourceKernel.bilinear_eq_squareCross _ _ z ζ
  rw [he]
  refine ⟨hQ.1.const_mul (-(Real.pi : ℂ)), ?_⟩
  have hscale : (∫ z : ℍ, ‖-(Real.pi : ℂ) * SourceKernel.squareCrossIntegral f z‖ ^ 2 ∂flatArea) =
      Real.pi ^ 2 * ∫ z : ℍ, ‖SourceKernel.squareCrossIntegral f z‖ ^ 2 ∂flatArea := by
    simp_rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, mul_pow]
    exact integral_const_mul _ _
  calc
    _ = _ := hscale
    _ ≤ Real.pi ^ 2 * (SourceKernel.squareRowMass ^ 2 * ∫ η : ℍ, ‖f η‖ ^ 2 ∂flatArea) :=
      mul_le_mul_of_nonneg_left hQ.2 (sq_nonneg _)
    _ ≤ Real.pi ^ 2 * (SourceKernel.squareRowMass ^ 2 *
        (‖c‖ ^ 2 * ‖b‖ ^ 2 * ∫ ξ : ℍ,
          ‖SourceKernel.cauchySquare (conj (ξ : ℂ)) ζ‖ ^ 2 ∂flatArea)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hout.2 (sq_nonneg _)) (sq_nonneg _)
    _ ≤ Real.pi ^ 2 * (SourceKernel.squareRowMass ^ 2 *
        (‖c‖ ^ 2 * ‖b‖ ^ 2 * (Real.pi / (4 * ζ.im ^ 2)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (SourceKernel.squareAnchor_integral_le ζ)
            (mul_nonneg (sq_nonneg _) (sq_nonneg _))) (sq_nonneg _)) (sq_nonneg _)
    _ = M * (ζ.im ^ 2)⁻¹ := by
      dsimp only [M]
      field_simp [pow_ne_zero 2 ζ.im_pos.ne']

private theorem native_sesquilinear_row_bound
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (u v : E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ : ℍ,
      MemLp (SourceKernel.sesquilinear (μ ν P F hF u) (μ ν P F hF v) ζ) 2 flatArea ∧
        (∫ z : ℍ, ‖SourceKernel.sesquilinear (μ ν P F hF u) (μ ν P F hF v) ζ z‖ ^ 2 ∂flatArea) ≤
          M * (ζ.im ^ 2)⁻¹ := by
  let := C
  let b : Ambient := (TH ν P F hF hsmooth ((K (β ν.val)).symm u)).val.val
  let c : Ambient := (TH ν P F hF hsmooth ((K (β ν.val)).symm v)).val.val
  let M : ℝ := SourceKernel.squareRowMass ^ 4 * ‖b‖ ^ 2 * ‖c‖ ^ 2 * Real.pi / 4
  refine ⟨M, by dsimp only [M]; positivity, fun ζ => ?_⟩
  have h := SourceKernel.sesquilinear_row_square_bound b c ζ
  refine ⟨h.1, ?_⟩
  calc
    _ ≤ SourceKernel.squareRowMass ^ 4 * ‖b‖ ^ 2 * ‖c‖ ^ 2 *
        ∫ ξ : ℍ, ‖SourceKernel.cauchySquare (conj (ξ : ℂ)) ζ‖ ^ 2 ∂flatArea := h.2
    _ ≤ SourceKernel.squareRowMass ^ 4 * ‖b‖ ^ 2 * ‖c‖ ^ 2 *
        (Real.pi / (4 * ζ.im ^ 2)) := mul_le_mul_of_nonneg_left
      (SourceKernel.squareAnchor_integral_le ζ) (by positivity)
    _ = M * (ζ.im ^ 2)⁻¹ := by
      dsimp only [M]
      field_simp [pow_ne_zero 2 ζ.im_pos.ne']

/-- The unchanged native four-direction source kernel has an integrable row
at every upper point, and its actual row integral is integrable over the
same given fundamental region. The original inner principal values and
concrete square-kernel bounds supply the convergence, with no final source
identity or curvature assumption. -/
theorem nativeWeilPetersson_four_integrable
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (u v w s : E) :
    (∀ ζ : ℍ, Integrable (SourceKernel.four
      (μ ν P F hF u) (μ ν P F hF v) (μ ν P F hF w) (μ ν P F hF s) ζ) flatArea) ∧
    IntegrableOn (fun ζ => ∫ z : ℍ, SourceKernel.four
      (μ ν P F hF u) (μ ν P F hF v) (μ ν P F hF w) (μ ν P F hF s) ζ z ∂flatArea) F flatArea := by
  let := C
  let b : E → Ambient := fun a => (TH ν P F hF hsmooth ((K (β ν.val)).symm a)).val.val
  let A : E → E → ℍ → ℍ → ℂ := fun a c =>
    SourceKernel.bilinear (μ ν P F hF a) (μ ν P F hF c)
  let B : E → E → ℍ → ℍ → ℂ := fun a c =>
    SourceKernel.sesquilinear (μ ν P F hF a) (μ ν P F hF c)
  have hA (a c : E) : StronglyMeasurable (fun p : ℍ × ℍ => A a c p.1 p.2) := by
    exact SourceKernel.square_bilinear_stronglyMeasurable (b a) (b c)
      (fun z ξ => nativeWeilPetersson_inner_principalValueExists
        R hp hg hgenus hΓ hfree hsmooth ν P F hF c z ξ)
  have hB (a c : E) : StronglyMeasurable (fun p : ℍ × ℍ => B a c p.1 p.2) :=
    SourceKernel.square_sesquilinear_stronglyMeasurable (b a) (b c)
  have hFour : StronglyMeasurable (fun p : ℍ × ℍ => SourceKernel.four
      (μ ν P F hF u) (μ ν P F hF v) (μ ν P F hF w) (μ ν P F hF s) p.1 p.2) :=
    (((hA u w).add (hA w u)).mul ((hA v s).add (hA s v)).star).add
      ((stronglyMeasurable_const.mul (hB u v)).mul (hB s w).star)
  obtain ⟨Ma, _, ha⟩ := native_bilinear_row_bound R hp hg hgenus hΓ hfree hsmooth ν P F hF u w
  obtain ⟨Mb, _, hb⟩ := native_bilinear_row_bound R hp hg hgenus hΓ hfree hsmooth ν P F hF w u
  obtain ⟨Mc, _, hc⟩ := native_bilinear_row_bound R hp hg hgenus hΓ hfree hsmooth ν P F hF v s
  obtain ⟨Md, _, hd⟩ := native_bilinear_row_bound R hp hg hgenus hΓ hfree hsmooth ν P F hF s v
  obtain ⟨Me, _, he⟩ := native_sesquilinear_row_bound R hp hg hgenus hΓ hfree hsmooth ν P F hF u v
  obtain ⟨Mf, _, hf⟩ := native_sesquilinear_row_bound R hp hg hgenus hΓ hfree hsmooth ν P F hF s w
  have hinner (ζ : ℍ) : Integrable (SourceKernel.four
      (μ ν P F hF u) (μ ν P F hF v) (μ ν P F hF w) (μ ν P F hF s) ζ) flatArea := by
    have hfirst := ((ha ζ).1.add (hb ζ).1).integrable_mul
      (SourceKernel.squareConj_memLp_two _ ((hc ζ).1.add (hd ζ).1))
    have hsecond := ((he ζ).1.const_mul (2 : ℂ)).integrable_mul
      (SourceKernel.squareConj_memLp_two _ (hf ζ).1)
    exact (hfirst.add hsecond).congr (Eventually.of_forall fun z => by rfl)
  let M : ℝ := Ma + Mb + Mc + Md + Me + Mf
  have hmass (ζ : ℍ) : (∫ z : ℍ, ‖SourceKernel.four
      (μ ν P F hF u) (μ ν P F hF v) (μ ν P F hF w) (μ ν P F hF s) ζ z‖ ∂flatArea) ≤
        M * (ζ.im ^ 2)⁻¹ := by
    have haSq : Integrable (fun z : ℍ => ‖A u w ζ z‖ ^ 2) flatArea :=
      (memLp_two_iff_integrable_sq_norm (ha ζ).1.aestronglyMeasurable).1 (ha ζ).1
    have hbSq : Integrable (fun z : ℍ => ‖A w u ζ z‖ ^ 2) flatArea :=
      (memLp_two_iff_integrable_sq_norm (hb ζ).1.aestronglyMeasurable).1 (hb ζ).1
    have hcSq : Integrable (fun z : ℍ => ‖A v s ζ z‖ ^ 2) flatArea :=
      (memLp_two_iff_integrable_sq_norm (hc ζ).1.aestronglyMeasurable).1 (hc ζ).1
    have hdSq : Integrable (fun z : ℍ => ‖A s v ζ z‖ ^ 2) flatArea :=
      (memLp_two_iff_integrable_sq_norm (hd ζ).1.aestronglyMeasurable).1 (hd ζ).1
    have heSq : Integrable (fun z : ℍ => ‖B u v ζ z‖ ^ 2) flatArea :=
      (memLp_two_iff_integrable_sq_norm (he ζ).1.aestronglyMeasurable).1 (he ζ).1
    have hfSq : Integrable (fun z : ℍ => ‖B s w ζ z‖ ^ 2) flatArea :=
      (memLp_two_iff_integrable_sq_norm (hf ζ).1.aestronglyMeasurable).1 (hf ζ).1
    let major : ℍ → ℝ := fun z => ‖A u w ζ z‖ ^ 2 + ‖A w u ζ z‖ ^ 2 +
      ‖A v s ζ z‖ ^ 2 + ‖A s v ζ z‖ ^ 2 + ‖B u v ζ z‖ ^ 2 + ‖B s w ζ z‖ ^ 2
    have hmajor : Integrable major flatArea :=
      ((((haSq.add hbSq).add hcSq).add hdSq).add heSq).add hfSq
    calc
      _ ≤ ∫ z : ℍ, major z ∂flatArea :=
        integral_mono_ae (hinner ζ).norm hmajor (Eventually.of_forall fun z =>
          SourceKernel.square_four_norm_le (A u w ζ z) (A w u ζ z)
            (A v s ζ z) (A s v ζ z) (B u v ζ z) (B s w ζ z))
      _ = (∫ z : ℍ, ‖A u w ζ z‖ ^ 2 ∂flatArea) +
          (∫ z : ℍ, ‖A w u ζ z‖ ^ 2 ∂flatArea) +
          (∫ z : ℍ, ‖A v s ζ z‖ ^ 2 ∂flatArea) +
          (∫ z : ℍ, ‖A s v ζ z‖ ^ 2 ∂flatArea) +
          (∫ z : ℍ, ‖B u v ζ z‖ ^ 2 ∂flatArea) +
          (∫ z : ℍ, ‖B s w ζ z‖ ^ 2 ∂flatArea) := by
        have hab := integral_add haSq hbSq
        have habc := integral_add (haSq.add hbSq) hcSq
        have habcd := integral_add ((haSq.add hbSq).add hcSq) hdSq
        have habcde := integral_add (((haSq.add hbSq).add hcSq).add hdSq) heSq
        have habcdef := integral_add ((((haSq.add hbSq).add hcSq).add hdSq).add heSq) hfSq
        simp only [Pi.add_apply] at habc habcd habcde habcdef
        dsimp only [major]
        rw [habcdef, habcde, habcd, habc, hab]
      _ ≤ Ma * (ζ.im ^ 2)⁻¹ + Mb * (ζ.im ^ 2)⁻¹ + Mc * (ζ.im ^ 2)⁻¹ +
          Md * (ζ.im ^ 2)⁻¹ + Me * (ζ.im ^ 2)⁻¹ + Mf * (ζ.im ^ 2)⁻¹ :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (ha ζ).2 (hb ζ).2)
          (hc ζ).2) (hd ζ).2) (he ζ).2) (hf ζ).2
      _ = M * (ζ.im ^ 2)⁻¹ := by dsimp only [M]; ring
  refine ⟨hinner, ?_⟩
  let f : ℍ → ℂ := fun ζ => ∫ z : ℍ, SourceKernel.four
    (μ ν P F hF u) (μ ν P F hF v) (μ ν P F hF w) (μ ν P F hF s) ζ z ∂flatArea
  have hfm : StronglyMeasurable f := hFour.integral_prod_right' (ν := flatArea)
  have hweighted (ζ : ℍ) : ‖f ζ‖ * ζ.im ^ 2 ≤ M := by
    apply (le_div_iff₀ (sq_pos_of_pos ζ.im_pos)).mp
    simpa only [div_eq_mul_inv] using (norm_integral_le_integral_norm _).trans (hmass ζ)
  let fp : ℂ → ℂ := SourceKernel.upperExtension f
  have hfpm : AEStronglyMeasurable fp (volume.restrict LiZhongQC.upperHalf) :=
    (SourceKernel.square_upperExtension_measurable f hfm.measurable).aestronglyMeasurable
  have hbound : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf), ‖fp z‖ * z.im ^ 2 ≤ M := by
    refine ⟨M, ae_restrict_of_forall_mem LiZhongQC.isOpen_upperHalf.measurableSet fun z hz => ?_⟩
    simpa only [fp, SourceKernel.upperExtension, show 0 < z.im from hz, dite_true,
      UpperHalfPlane.im] using hweighted ⟨z, hz⟩
  let S := deformedNativeSurface R hgenus hΓ hp ν
  let := S.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.isManifold
  let := S.t2Space
  let := S.connectedSpace
  let := S.compactSpace
  have hcover := deformedNativeSurface_uniformization R hgenus hΓ hp ν
  have hi := sourceFundamentalDomainH_integrable_of_weighted_bound
    S (LiZhongQC.utm_x_isFuchsian hcover)
    hcover (Fuchsian.closedPlanarRegion_isFundamentalDomainH P hF) hfpm hbound
  have ho := (Fuchsian.integrableOn_openPlanarRegion_iff_closedPlanarRegion
    hF.1 hF.2.2.2 fp).mpr hi
  have hflat := (UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
    (image_subset_range UpperHalfPlane.coe F)).mp ho
  have hext : fp ∘ UpperHalfPlane.coe = f := by
    funext ζ
    change (if hz : 0 < (ζ : ℂ).im then f ⟨(ζ : ℂ), hz⟩ else 0) = f ζ
    rw [dite_eq_left (show 0 < (ζ : ℂ).im from ζ.im_pos)]
  change IntegrableOn (fp ∘ UpperHalfPlane.coe)
    (UpperHalfPlane.coe ⁻¹' (UpperHalfPlane.coe '' F)) flatArea at hflat
  simpa only [hext, UpperHalfPlane.coe_injective.preimage_image] using hflat

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth

/-- The individual original bilinear product is absolutely integrable on
its actual fundamental-region cylinder. This uses its three actual square
row bounds, rather than extracting a summand from a convergent sum. -/
theorem nativeWeilPetersson_bilinear_product_integrable
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (u v w s : E) :
    Integrable (fun q : ℍ × ℍ =>
      SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF w) q.1 q.2 *
        conj (SourceKernel.bilinear (μ ν P F hF v) (μ ν P F hF s) q.1 q.2 +
          SourceKernel.bilinear (μ ν P F hF s) (μ ν P F hF v) q.1 q.2))
      ((flatArea.restrict F).prod flatArea) := by
  let := C
  let b : E → Ambient := fun a => (TH ν P F hF hsmooth ((K (β ν.val)).symm a)).val.val
  let A : E → E → ℍ → ℍ → ℂ := fun a c =>
    SourceKernel.bilinear (μ ν P F hF a) (μ ν P F hF c)
  let Φ : ℍ × ℍ → ℂ := fun q => A u w q.1 q.2 * conj (A v s q.1 q.2 + A s v q.1 q.2)
  have hA (a c : E) : StronglyMeasurable (fun q : ℍ × ℍ => A a c q.1 q.2) :=
    SourceKernel.square_bilinear_stronglyMeasurable (b a) (b c)
      (fun z ξ => nativeWeilPetersson_inner_principalValueExists
        R hp hg hgenus hΓ hfree hsmooth ν P F hF c z ξ)
  have hΦ : StronglyMeasurable Φ := (hA u w).mul ((hA v s).add (hA s v)).star
  obtain ⟨Ma, _, ha⟩ := native_bilinear_row_bound R hp hg hgenus hΓ hfree hsmooth ν P F hF u w
  obtain ⟨Mb, _, hb⟩ := native_bilinear_row_bound R hp hg hgenus hΓ hfree hsmooth ν P F hF v s
  obtain ⟨Mc, _, hc⟩ := native_bilinear_row_bound R hp hg hgenus hΓ hfree hsmooth ν P F hF s v
  have hinner (ζ : ℍ) : Integrable (fun z : ℍ => Φ (ζ, z)) flatArea := by
    simpa only [Φ, A, Pi.mul_def, Pi.add_def] using ((ha ζ).1.integrable_mul
      (SourceKernel.squareConj_memLp_two _ ((hb ζ).1.add (hc ζ).1)))
  let M : ℝ := Ma + Mb + Mc
  have hmass (ζ : ℍ) : (∫ z : ℍ, ‖Φ (ζ, z)‖ ∂flatArea) ≤ M * (ζ.im ^ 2)⁻¹ := by
    have haSq : Integrable (fun z : ℍ => ‖A u w ζ z‖ ^ 2) flatArea :=
      (memLp_two_iff_integrable_sq_norm (ha ζ).1.aestronglyMeasurable).1 (ha ζ).1
    have hbSq : Integrable (fun z : ℍ => ‖A v s ζ z‖ ^ 2) flatArea :=
      (memLp_two_iff_integrable_sq_norm (hb ζ).1.aestronglyMeasurable).1 (hb ζ).1
    have hcSq : Integrable (fun z : ℍ => ‖A s v ζ z‖ ^ 2) flatArea :=
      (memLp_two_iff_integrable_sq_norm (hc ζ).1.aestronglyMeasurable).1 (hc ζ).1
    let major : ℍ → ℝ := fun z => ‖A u w ζ z‖ ^ 2 + ‖A v s ζ z‖ ^ 2 + ‖A s v ζ z‖ ^ 2
    have hmajor : Integrable major flatArea := (haSq.add hbSq).add hcSq
    calc
      _ ≤ ∫ z : ℍ, major z ∂flatArea := by
        apply integral_mono_ae (hinner ζ).norm hmajor
        exact Eventually.of_forall fun z => by
          simpa only [Φ, add_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
            mul_zero, zero_mul] using
            SourceKernel.square_four_norm_le (A u w ζ z) 0 (A v s ζ z) (A s v ζ z) 0 0
      _ = (∫ z : ℍ, ‖A u w ζ z‖ ^ 2 ∂flatArea) +
          (∫ z : ℍ, ‖A v s ζ z‖ ^ 2 ∂flatArea) +
          (∫ z : ℍ, ‖A s v ζ z‖ ^ 2 ∂flatArea) := by
        have hab := integral_add haSq hbSq
        have habc := integral_add (haSq.add hbSq) hcSq
        simp only [Pi.add_apply] at habc
        dsimp only [major]
        rw [habc, hab]
      _ ≤ Ma * (ζ.im ^ 2)⁻¹ + Mb * (ζ.im ^ 2)⁻¹ + Mc * (ζ.im ^ 2)⁻¹ :=
        add_le_add (add_le_add (ha ζ).2 (hb ζ).2) (hc ζ).2
      _ = M * (ζ.im ^ 2)⁻¹ := by dsimp only [M]; ring
  let mass : ℍ → ℝ := fun ζ => ∫ z : ℍ, ‖Φ (ζ, z)‖ ∂flatArea
  let fc : ℍ → ℂ := fun ζ => (mass ζ : ℂ)
  have hfm : StronglyMeasurable fc :=
    Complex.continuous_ofReal.comp_stronglyMeasurable (hΦ.norm.integral_prod_right' (ν := flatArea))
  have hweighted (ζ : ℍ) : ‖fc ζ‖ * ζ.im ^ 2 ≤ M := by
    have hnn : 0 ≤ mass ζ := integral_nonneg fun z => norm_nonneg _
    apply (le_div_iff₀ (sq_pos_of_pos ζ.im_pos)).mp
    simpa only [fc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn, div_eq_mul_inv] using
      hmass ζ
  let fp : ℂ → ℂ := SourceKernel.upperExtension fc
  have hfpm : AEStronglyMeasurable fp (volume.restrict LiZhongQC.upperHalf) :=
    (SourceKernel.square_upperExtension_measurable fc hfm.measurable).aestronglyMeasurable
  have hbound : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf), ‖fp z‖ * z.im ^ 2 ≤ M := by
    refine ⟨M, ae_restrict_of_forall_mem LiZhongQC.isOpen_upperHalf.measurableSet fun z hz => ?_⟩
    simpa only [fp, SourceKernel.upperExtension, show 0 < z.im from hz, dite_true,
      UpperHalfPlane.im] using hweighted ⟨z, hz⟩
  let S := deformedNativeSurface R hgenus hΓ hp ν
  let := S.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.isManifold
  let := S.t2Space
  let := S.connectedSpace
  let := S.compactSpace
  have hcover := deformedNativeSurface_uniformization R hgenus hΓ hp ν
  have hi := sourceFundamentalDomainH_integrable_of_weighted_bound
    S (LiZhongQC.utm_x_isFuchsian hcover)
    hcover (Fuchsian.closedPlanarRegion_isFundamentalDomainH P hF) hfpm hbound
  have ho := (Fuchsian.integrableOn_openPlanarRegion_iff_closedPlanarRegion
    hF.1 hF.2.2.2 fp).mpr hi
  have hflat := (UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
    (image_subset_range UpperHalfPlane.coe F)).mp ho
  have hext : fp ∘ UpperHalfPlane.coe = fc := by
    funext ζ
    change (if hz : 0 < (ζ : ℂ).im then fc ⟨(ζ : ℂ), hz⟩ else 0) = fc ζ
    rw [dite_eq_left (show 0 < (ζ : ℂ).im from ζ.im_pos)]
  have hfc : IntegrableOn fc F flatArea := by
    change IntegrableOn (fp ∘ UpperHalfPlane.coe)
      (UpperHalfPlane.coe ⁻¹' (UpperHalfPlane.coe '' F)) flatArea at hflat
    simpa only [hext, UpperHalfPlane.coe_injective.preimage_image] using hflat
  have hnorm : Integrable mass (flatArea.restrict F) := by
    unfold IntegrableOn at hfc
    simpa only [fc, RCLike.re_eq_complex_re, Complex.ofReal_re] using hfc.re
  exact (integrable_prod_iff hΦ.aestronglyMeasurable).2 ⟨Eventually.of_forall hinner, hnorm⟩

section BilinearDomain

variable (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (u v w s : Fin (3 * g - 3) → ℂ)

local notation "Φ" => (fun q : ℍ × ℍ =>
  SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF w) (Prod.fst q) (Prod.snd q) *
    conj (SourceKernel.bilinear (μ ν P F hF v) (μ ν P F hF s) (Prod.fst q) (Prod.snd q) +
      SourceKernel.bilinear (μ ν P F hF s) (μ ν P F hF v) (Prod.fst q) (Prod.snd q)))
local notation "Ω" => (fun q : ℍ × ℍ =>
  ((UpperHalfPlane.im (Prod.fst q) : ℂ) ^ 2 *
    (UpperHalfPlane.im (Prod.snd q) : ℂ) ^ 2) * Φ q)
local notation "μ₂" => (Measure.prod (volume : Measure ℍ) (volume : Measure ℍ))
local notation "λ₂" => (Measure.prod flatArea flatArea)

private theorem bilinear_domain_height (γ : Deck) (z : ℍ) :
    ((γ • z : ℍ).im : ℂ) = (z.im : ℂ) /
      (denominator γ z * conj (denominator γ z)) := by
  have him : (γ • z : ℍ).im = z.im / Complex.normSq (denominator γ z) := by
    simp [MulAction.compHom_smul_def, UpperHalfPlane.im_smul_eq_div_normSq,
      Matrix.SpecialLinearGroup.det_mapGL, UpperHalfPlane.denom, denominator]
  rw [Complex.mul_conj]
  exact_mod_cast him

include g R hp hg hgenus hΓ hfree hsmooth ν P F hF u v w s in
private theorem native_bilinear_product_density_deck
    (γ : Deck) (hγ : γ ∈ deformedGroup hΓ ν) (q : ℍ × ℍ) : Ω (γ • q) = Ω q := by
  simp only [Prod.smul_fst, Prod.smul_snd]
  rw [bilinear_domain_height, bilinear_domain_height,
    nativeWeilPetersson_bilinear_deck R hp hg hgenus hΓ hfree hsmooth ν P F hF u w γ hγ q.1 q.2,
    nativeWeilPetersson_bilinear_deck R hp hg hgenus hΓ hfree hsmooth ν P F hF v s γ hγ q.1 q.2,
    nativeWeilPetersson_bilinear_deck R hp hg hgenus hΓ hfree hsmooth ν P F hF s v γ hγ q.1 q.2]
  have hdc (z : ℍ) : conj (denominator γ z) ≠ 0 := by
    intro hz
    apply denominator_ne_zero γ z
    simpa only [Complex.conj_conj, map_zero] using congrArg conj hz
  simp only [map_mul, map_add, map_pow, Complex.conj_conj]
  field_simp [denominator_ne_zero γ q.1, denominator_ne_zero γ q.2, hdc q.1, hdc q.2]

include g R hp hg hgenus hΓ hfree hsmooth ν P F hF u v w s in
private theorem native_bilinear_product_density_to_flat
    (S : Set (ℍ × ℍ)) (hS : MeasurableSet S) :
    (∫ q in S, Ω q ∂μ₂) = ∫ q in S, Φ q ∂λ₂ := by
  let ρ : ℍ × ℍ → ℝ≥0∞ := fun q => hyperbolicDensity q.1 * hyperbolicDensity q.2
  have hm : Measurable ρ := (measurable_hyperbolicDensity.comp measurable_fst).mul
    (measurable_hyperbolicDensity.comp measurable_snd)
  have hf (q : ℍ × ℍ) : ρ q < ⊤ :=
    ENNReal.mul_lt_top (by simp [hyperbolicDensity]) (by simp [hyperbolicDensity])
  have hvol : μ₂ = λ₂.withDensity ρ := by
    change (flatArea.withDensity hyperbolicDensity).prod (flatArea.withDensity hyperbolicDensity) = _
    exact MeasureTheory.prod_withDensity measurable_hyperbolicDensity measurable_hyperbolicDensity
  rw [hvol, MeasureTheory.restrict_withDensity hS ρ,
    integral_withDensity_eq_integral_toReal_smul hm (Eventually.of_forall hf)]
  apply integral_congr_ae
  exact Eventually.of_forall fun q => by
    simp only [ρ, ENNReal.toReal_mul, hyperbolicDensity, ENNReal.coe_toReal,
      NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk, Complex.real_smul]
    push_cast
    field_simp [q.1.im_ne_zero, q.2.im_ne_zero]

include g R hp hg hgenus hΓ hfree hsmooth ν P F hF u v w s in
private theorem native_bilinear_product_cylinder_integral :
    (∫ q : ℍ × ℍ in F ×ˢ (univ : Set ℍ), Φ q ∂λ₂) =
      ∫ q : ℍ × ℍ in (univ : Set ℍ) ×ˢ F, Φ q ∂λ₂ := by
  let G := (deformedGroup hΓ ν).map Hyperbolic.realSLMobius
  let := P.nativeAction
  let : Countable G := Mobius.discreteMobius_countable G P.discrete
  have hmp (a : G) : MeasurePreserving (fun q : ℍ × ℍ => a • q) μ₂ μ₂ := by
    have h := Hyperbolic.nativeIsometry_measurePreserving (P.nativeHom a)
    exact h.prod h
  let : MeasurableConstSMul G (ℍ × ℍ) := ⟨fun a => (hmp a).measurable⟩
  let : SMulInvariantMeasure G (ℍ × ℍ) μ₂ :=
    ⟨fun a S hS => (hmp a).measure_preimage hS.nullMeasurableSet⟩
  have hfund := hF.measureFundamentalDomain P
  have hfirst : MeasureTheory.IsFundamentalDomain G (F ×ˢ (univ : Set ℍ)) μ₂ := by
    rw [Set.prod_univ]
    exact hfund.preimage_of_equiv
      (show QuasiMeasurePreserving Prod.fst μ₂ (volume : Measure ℍ) from
        Measure.quasiMeasurePreserving_fst)
      Function.bijective_id (fun _ _ => rfl)
  have hsecond : MeasureTheory.IsFundamentalDomain G ((univ : Set ℍ) ×ˢ F) μ₂ := by
    rw [Set.univ_prod]
    exact hfund.preimage_of_equiv
      (show QuasiMeasurePreserving Prod.snd μ₂ (volume : Measure ℍ) from
        Measure.quasiMeasurePreserving_snd)
      Function.bijective_id (fun _ _ => rfl)
  have hinv (a : G) (q : ℍ × ℍ) : Ω (a • q) = Ω q := by
    obtain ⟨A, hA, hAa⟩ := Subgroup.mem_map.mp a.property
    change Ω (a • q.1, a • q.2) = _
    rw [P.nativeAction_realSL a A hAa q.1, P.nativeAction_realSL a A hAa q.2]
    exact native_bilinear_product_density_deck R hp hg hgenus hΓ hfree hsmooth ν P F hF u v w s A hA q
  have he := hfirst.setIntegral_eq hsecond (f := Ω) hinv
  rw [native_bilinear_product_density_to_flat R hp hg hgenus hΓ hfree hsmooth ν P F hF u v w s
      (F ×ˢ (univ : Set ℍ)) (hF.1.measurableSet.prod MeasurableSet.univ),
    native_bilinear_product_density_to_flat R hp hg hgenus hΓ hfree hsmooth ν P F hF u v w s
      ((univ : Set ℍ) ×ˢ F) (MeasurableSet.univ.prod hF.1.measurableSet)] at he
  exact he

include g R hp hg hgenus hΓ hfree hsmooth ν P F hF u v w s in
/-- The two actual integration orders for the original bilinear product
agree on the same given fundamental region. Both product integrals are
absolutely convergent before applying the fundamental-domain equality
and Fubini; the inner singularity remains its actual principal value. -/
theorem nativeWeilPetersson_bilinear_product_domain_exchange :
    (∫ ζ in F, ∫ z : ℍ, Φ (ζ, z) ∂flatArea ∂flatArea) =
      ∫ ζ in F, ∫ z : ℍ, Φ (z, ζ) ∂flatArea ∂flatArea := by
  have hfirst := nativeWeilPetersson_bilinear_product_integrable
    R hp hg hgenus hΓ hfree hsmooth ν P F hF u v w s
  have hswap : Φ ∘ Prod.swap = (fun q : ℍ × ℍ =>
      SourceKernel.bilinear (μ ν P F hF w) (μ ν P F hF u) q.1 q.2 *
        conj (SourceKernel.bilinear (μ ν P F hF v) (μ ν P F hF s) q.1 q.2 +
          SourceKernel.bilinear (μ ν P F hF s) (μ ν P F hF v) q.1 q.2)) := by
    funext q
    change SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF w) q.2 q.1 *
      conj (SourceKernel.bilinear (μ ν P F hF v) (μ ν P F hF s) q.2 q.1 +
        SourceKernel.bilinear (μ ν P F hF s) (μ ν P F hF v) q.2 q.1) = _
    rw [nativeWeilPetersson_bilinear_transpose R hp hg hgenus hΓ hfree hsmooth ν P F hF u w q.2 q.1,
      nativeWeilPetersson_bilinear_transpose R hp hg hgenus hΓ hfree hsmooth ν P F hF v s q.2 q.1,
      nativeWeilPetersson_bilinear_transpose R hp hg hgenus hΓ hfree hsmooth ν P F hF s v q.2 q.1,
      add_comm]
  have hlast : Integrable Φ (flatArea.prod (flatArea.restrict F)) := by
    apply integrable_swap_iff.mp
    rw [hswap]
    exact nativeWeilPetersson_bilinear_product_integrable
      R hp hg hgenus hΓ hfree hsmooth ν P F hF w v u s
  have hfirstSet : IntegrableOn Φ (F ×ˢ (univ : Set ℍ)) λ₂ := by
    unfold IntegrableOn
    rw [← Measure.prod_restrict, Measure.restrict_univ]
    exact hfirst
  have hlastSet : IntegrableOn Φ ((univ : Set ℍ) ×ˢ F) λ₂ := by
    unfold IntegrableOn
    rw [← Measure.prod_restrict, Measure.restrict_univ]
    exact hlast
  have he := native_bilinear_product_cylinder_integral R hp hg hgenus hΓ hfree hsmooth ν P F hF u v w s
  rw [setIntegral_prod Φ hfirstSet, setIntegral_prod Φ hlastSet] at he
  simp only [setIntegral_univ] at he
  calc
    _ = ∫ ζ : ℍ, ∫ z in F, Φ (ζ, z) ∂flatArea ∂flatArea := he
    _ = _ := integral_integral_swap hlast

end BilinearDomain

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth

/-- Each actual bilinear kernel is square integrable on the same given
fundamental-region cylinder, using its original completed Hilbert pairing. -/
theorem nativeWeilPetersson_bilinear_region_memLp_two
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (u w : E) :
    MemLp (fun a : ℍ × ℍ => SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF w) a.1 a.2) 2
      ((flatArea.restrict F).prod flatArea) := by
  let := C
  let b : E → Ambient := fun a => (TH ν P F hF hsmooth ((K (β ν.val)).symm a)).val.val
  let A : ℍ × ℍ → ℂ := fun a => SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF w) a.1 a.2
  have hA : StronglyMeasurable A := SourceKernel.square_bilinear_stronglyMeasurable (b u) (b w)
    (fun z ξ => nativeWeilPetersson_inner_principalValueExists
      R hp hg hgenus hΓ hfree hsmooth ν P F hF w z ξ)
  obtain ⟨M, hM, hb⟩ := native_bilinear_row_bound R hp hg hgenus hΓ hfree hsmooth ν P F hF u w
  have hheight := SourceKernel.square_inverseHeight_integrable
    (deformedNativeSurface R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) P F hF
  have hmass : Integrable (fun ζ : ℍ => ∫ z : ℍ, ‖A (ζ, z)‖ ^ 2 ∂flatArea)
      (flatArea.restrict F) := by
    apply (hheight.const_mul M).mono'
      (hA.norm.pow 2).integral_prod_right'.aestronglyMeasurable
    exact Eventually.of_forall fun ζ => by
      change ‖∫ z : ℍ, ‖A (ζ, z)‖ ^ 2 ∂flatArea‖ ≤ M * (ζ.im ^ 2)⁻¹
      rw [Real.norm_of_nonneg (integral_nonneg fun z => sq_nonneg _)]
      exact (hb ζ).2
  have hsq : Integrable (fun a : ℍ × ℍ => ‖A a‖ ^ 2)
      ((flatArea.restrict F).prod flatArea) := by
    apply (integrable_prod_iff (hA.norm.pow 2).aestronglyMeasurable).2
    refine ⟨Eventually.of_forall (fun ζ =>
      (memLp_two_iff_integrable_sq_norm (hb ζ).1.aestronglyMeasurable).1 (hb ζ).1), ?_⟩
    simpa only [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)] using hmass
  exact (memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).2 hsq

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace


namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open Surfaces LiZhongQC GammaMeasurableBeltrami

/-- The original outer bilinear pairing after its positive invariant
exclusion of the inner same-half-plane pole. -/
def invariantBilinear (μ ν : ℍ → ℂ) (e : ℝ) (ζ z : ℍ) : ℂ :=
  -(Real.pi : ℂ) * ∫ η : ℍ, μ η * cauchySquare η (conj (ζ : ℂ)) *
    (-(1 / (Real.pi : ℂ)) *
      ∫ ρ : ℂ in {ρ : ℂ | e * ‖ρ - conj (η : ℂ)‖ < ‖ρ - (η : ℂ)‖},
        innerInput ν z ρ / (ρ - η) ^ 2) ∂flatArea

private theorem cut_innerInput_identity (μ : ℍ → ℂ) (z : ℍ) (ρ : ℂ) :
    innerInput μ z ρ = upperExtension μ ρ * cauchySquare ρ (conj (z : ℂ)) := by
  by_cases hρ : 0 < ρ.im
  · simp only [innerInput, upperExtension, hρ, dite_true]
  · simp only [innerInput, upperExtension, hρ, dite_false, zero_mul]

private theorem cut_outerInput_identity (μ ν : ℍ → ℂ) (z : ℍ) (η : ℂ) :
    outerInput μ ν z η = upperExtension μ η * hilbertHSmooth (innerInput ν z) η := by
  by_cases hη : 0 < η.im
  · simp only [outerInput, upperExtension, hη, dite_true]
  · simp only [outerInput, upperExtension, hη, dite_false, zero_mul]

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)

private theorem cut_coefficient_flat_ae (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) =ᵐ[flatArea]
      NativeHarmonicBeltrami.coefficient R p q :=
  ae_hyperbolic_iff.mp (NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp q)

private theorem cut_upperExtension_ae (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    upperExtension (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) =ᵐ[volume]
      upperExtension (NativeHarmonicBeltrami.coefficient R p q) := by
  apply ae_of_ae_restrict_of_ae_restrict_compl upperHalf
  · rw [← map_flat_coe, UpperHalfPlane.measurableEmbedding_coe.ae_map_iff]
    filter_upwards [cut_coefficient_flat_ae R p hp q] with η hη
    simpa only [upperExtension, dite_eq_left (show 0 < (η : ℂ).im from η.im_pos)] using hη
  · exact ae_restrict_of_forall_mem isOpen_upperHalf.measurableSet.compl fun η hη => by
      simp only [upperExtension, show ¬0 < η.im from hη, dite_false]

private theorem cut_input_ae (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    innerInput (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) z =ᵐ[volume]
      innerInput (NativeHarmonicBeltrami.coefficient R p q) z := by
  filter_upwards [cut_upperExtension_ae R p hp q] with ρ hρ
  simp only [cut_innerInput_identity, hρ]

private theorem cut_bilinear_chosen_literal
    (u q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (ζ z : ℍ) :
    bilinear (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp u).val η)
      (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) ζ z =
    bilinear (NativeHarmonicBeltrami.coefficient R p u)
      (NativeHarmonicBeltrami.coefficient R p q) ζ z := by
  have hH := hilbertHSmooth_congr_ae (cut_input_ae R p hp q z)
  have hout : outerInput (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp u).val η)
      (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) z =ᵐ[volume]
      outerInput (NativeHarmonicBeltrami.coefficient R p u)
        (NativeHarmonicBeltrami.coefficient R p q) z := by
    filter_upwards [cut_upperExtension_ae R p hp u] with η hη
    simp only [cut_outerInput_identity, hη, hH]
  unfold bilinear
  rw [hilbertHSmooth_congr_ae hout]

private theorem cut_invariant_chosen_literal
    (u q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (e : ℝ) (ζ z : ℍ) :
    invariantBilinear (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp u).val η)
      (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) e ζ z =
      bilinearInvariantTruncation R p q u e ζ z := by
  have hI (η : ℍ) : (∫ ρ : ℂ in {ρ : ℂ | e * ‖ρ - conj (η : ℂ)‖ < ‖ρ - (η : ℂ)‖},
      innerInput (fun w => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val w) z ρ /
        (ρ - η) ^ 2) =
      ∫ ρ : ℂ in {ρ : ℂ | e * ‖ρ - conj (η : ℂ)‖ < ‖ρ - (η : ℂ)‖},
        innerInput (NativeHarmonicBeltrami.coefficient R p q) z ρ / (ρ - η) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (cut_input_ae R p hp q z)] with ρ hρ
    rw [hρ]
  change -(Real.pi : ℂ) * _ = -(Real.pi : ℂ) * _
  congr 1
  apply integral_congr_ae
  filter_upwards [cut_coefficient_flat_ae R p hp u] with η hη
  change _ * _ * (_ * _) = _ * _ * (_ * _)
  simp only [actualInvariantExterior]
  rw [hη, hI η]

include hp in
private theorem cut_literal_stronglyMeasurable
    (u q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (e : ℝ) :
    StronglyMeasurable (fun a : ℍ × ℍ => bilinearInvariantTruncation R p q u e a.1 a.2) := by
  let μ := NativeHarmonicBeltrami.coefficient R p u
  let ν := NativeHarmonicBeltrami.coefficient R p q
  let J : (ℍ × ℍ) × ℂ → ℂ := fun a => innerInput ν a.1.1 a.2 / (a.2 - a.1.2) ^ 2
  let S : Set ((ℍ × ℍ) × ℂ) :=
    {a | e * ‖a.2 - conj (a.1.2 : ℂ)‖ < ‖a.2 - (a.1.2 : ℂ)‖}
  have hν : Measurable (upperExtension ν) := square_upperExtension_measurable _
    (NativeHarmonicBeltrami.coefficient_continuous R p hp q).measurable
  have hJ : Measurable J := by
    have heq : J = fun a => (upperExtension ν a.2 *
        cauchySquare a.2 (conj (a.1.1 : ℂ))) / (a.2 - a.1.2) ^ 2 := by
      funext a
      dsimp only [J]
      rw [cut_innerInput_identity]
    rw [heq]
    exact ((hν.comp measurable_snd).mul (by unfold cauchySquare; fun_prop)).div (by fun_prop)
  have hS : MeasurableSet S := measurableSet_lt (by fun_prop) (by fun_prop)
  let I : ℍ × ℍ → ℂ := fun a => -(1 / (Real.pi : ℂ)) *
    ∫ ρ : ℂ in {ρ : ℂ | e * ‖ρ - conj (a.2 : ℂ)‖ < ‖ρ - (a.2 : ℂ)‖},
      innerInput ν a.1 ρ / (ρ - a.2) ^ 2
  have hI : StronglyMeasurable I := by
    have hi := (hJ.stronglyMeasurable.indicator hS).integral_prod_right' (ν := (volume : Measure ℂ))
    have heq : I = fun a => -(1 / (Real.pi : ℂ)) * ∫ ρ : ℂ, S.indicator J (a, ρ) := by
      funext a
      dsimp only [I]
      congr 1
      rw [← integral_indicator (measurableSet_lt (by fun_prop) (by fun_prop))]
      rfl
    rw [heq]
    exact stronglyMeasurable_const.mul hi
  have hOuter : StronglyMeasurable (fun a : (ℍ × ℍ) × ℍ =>
      μ a.2 * cauchySquare a.2 (conj (a.1.1 : ℂ)) * I (a.1.2, a.2)) := by
    have hμ := (NativeHarmonicBeltrami.coefficient_continuous R p hp u).measurable
    have hk : Measurable (fun a : (ℍ × ℍ) × ℍ =>
        cauchySquare a.2 (conj (a.1.1 : ℂ))) := by unfold cauchySquare; fun_prop
    exact ((hμ.comp measurable_snd).stronglyMeasurable.mul hk.stronglyMeasurable).mul
      (hI.comp_measurable (measurable_fst.snd.prodMk measurable_snd))
  exact stronglyMeasurable_const.mul hOuter.integral_prod_right'

private theorem cut_ofQuadratic_bound
    (u q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ e : ℝ, StronglyMeasurable (fun a : ℍ × ℍ =>
        invariantBilinear (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp u).val η)
          (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) e a.1 a.2)) ∧
      ∀ (a : ℍ × ℍ) (e : ℝ), 0 < e → e < 1 / 16 →
        ‖invariantBilinear (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp u).val η)
            (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) e a.1 a.2 -
          bilinear (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp u).val η)
            (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) a.1 a.2‖ ≤
          C * e * absoluteCrossPair a.1 a.2 := by
  obtain ⟨C, hC, hb⟩ := bilinear_ofQuadratic_invariant_truncation_tendsto R p hp q u
  refine ⟨C, hC, ?_, ?_⟩
  · intro e
    have heq : (fun a : ℍ × ℍ =>
        invariantBilinear (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp u).val η)
          (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) e a.1 a.2) =
        fun a => bilinearInvariantTruncation R p q u e a.1 a.2 :=
      funext fun a => cut_invariant_chosen_literal R p hp u q e a.1 a.2
    rw [heq]
    exact cut_literal_stronglyMeasurable R p hp u q e
  · intro a e he0 he16
    rw [cut_invariant_chosen_literal R p hp u q e a.1 a.2,
      cut_bilinear_chosen_literal R p hp u q a.1 a.2, absoluteCrossPair_literal]
    exact ((hb a.1 a.2).1 e he0 he16).2

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel


namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth

private theorem native_invariantBilinear_control
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (u w : E) :
    ∃ D : ℝ, 0 ≤ D ∧
      (∀ e : ℝ, StronglyMeasurable (fun a : ℍ × ℍ =>
        SourceKernel.invariantBilinear (μ ν P F hF u) (μ ν P F hF w) e a.1 a.2)) ∧
      (∀ (a : ℍ × ℍ) (e : ℝ), 0 < e → e < 1 / 16 →
        ‖SourceKernel.invariantBilinear (μ ν P F hF u) (μ ν P F hF w) e a.1 a.2 -
          SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF w) a.1 a.2‖ ≤
          D * e * SourceKernel.absoluteCrossPair a.1 a.2) ∧
      ∀ a : ℍ × ℍ, Tendsto
        (fun e : ℝ => SourceKernel.invariantBilinear (μ ν P F hF u) (μ ν P F hF w) e a.1 a.2)
        (𝓝[>] (0 : ℝ))
        (𝓝 (SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF w) a.1 a.2)) := by
  let := C
  let bu := TH ν P F hF hsmooth ((K (β ν.val)).symm u)
  let bw := TH ν P F hF hsmooth ((K (β ν.val)).symm w)
  let S := deformedNativeSurface R hgenus hΓ hp ν
  have hcover := deformedNativeSurface_uniformization R hgenus hΓ hp ν
  rcases (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic S P
    (deformedTargetCover R hgenus hΓ hp ν) hcover F hF bu.val).mp bu.property with ⟨qu, hqu⟩
  rcases (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic S P
    (deformedTargetCover R hgenus hΓ hp ν) hcover F hF bw.val).mp bw.property with ⟨qw, hqw⟩
  obtain ⟨D, hD, hm, hb⟩ := SourceKernel.cut_ofQuadratic_bound S _ hcover qu qw
  have hlim (a : ℍ × ℍ) : Tendsto
      (fun e : ℝ => SourceKernel.invariantBilinear
        (fun η => (NativeHarmonicBeltrami.ofQuadratic S _ hcover qu).val η)
        (fun η => (NativeHarmonicBeltrami.ofQuadratic S _ hcover qw).val η) e a.1 a.2)
      (𝓝[>] (0 : ℝ)) (𝓝 (SourceKernel.bilinear
        (fun η => (NativeHarmonicBeltrami.ofQuadratic S _ hcover qu).val η)
        (fun η => (NativeHarmonicBeltrami.ofQuadratic S _ hcover qw).val η) a.1 a.2)) := by
    obtain ⟨_, _, ht⟩ := SourceKernel.bilinear_ofQuadratic_invariant_truncation_tendsto
      S _ hcover qw qu
    simpa only [SourceKernel.cut_invariant_chosen_literal,
      SourceKernel.cut_bilinear_chosen_literal] using (ht a.1 a.2).2
  rw [hqu, hqw] at hm hb hlim
  exact ⟨D, hD, hm, hb, hlim⟩

/-- The product of the two actual invariant-cut bilinear pairings has
absolute integrals on the original cylinder. Its reflected lower exclusion
is removed first, followed by the upper exclusion, inside those outer
integrals. The reversed case retains the second pair of points until its
completed limit, where the proved native transpose is used for L². The result
is the original completed bilinear product. -/
theorem nativeWeilPetersson_invariant_bilinear_product_ordered_tendsto
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (u v w s : E) (reverse : Bool) :
    let A : E → E → ℍ × ℍ → ℂ := fun a b q =>
      SourceKernel.bilinear (μ ν P F hF a) (μ ν P F hF b) q.1 q.2
    let cut : E → E → ℝ → ℍ × ℍ → ℂ := fun a b e q =>
      SourceKernel.invariantBilinear (μ ν P F hF a) (μ ν P F hF b) e q.1 q.2
    let lower : ℍ × ℍ → ℍ × ℍ := if reverse then Prod.swap else id
    let cylinderMeasure := (flatArea.restrict F).prod flatArea
    (∀ (e t : ℝ), 0 < e → e < 1 / 16 → 0 < t → t < 1 / 16 →
      Integrable (fun q : ℍ × ℍ => cut u w e q * conj (cut v s t (lower q))) cylinderMeasure) ∧
    (∀ e : ℝ, 0 < e → e < 1 / 16 →
      Integrable (fun q : ℍ × ℍ => cut u w e q * conj (A v s (lower q))) cylinderMeasure ∧
      Tendsto (fun t : ℝ => ∫ q : ℍ × ℍ, cut u w e q * conj (cut v s t (lower q)) ∂cylinderMeasure)
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ q : ℍ × ℍ, cut u w e q * conj (A v s (lower q)) ∂cylinderMeasure))) ∧
    Tendsto (fun e : ℝ => ∫ q : ℍ × ℍ, cut u w e q * conj (A v s (lower q)) ∂cylinderMeasure)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ q : ℍ × ℍ, A u w q * conj (A v s (lower q)) ∂cylinderMeasure)) ∧
    (Filter.limUnder (𝓝[>] (0 : ℝ)) fun e : ℝ =>
      Filter.limUnder (𝓝[>] (0 : ℝ)) fun t : ℝ =>
        ∫ q : ℍ × ℍ, cut u w e q * conj (cut v s t (lower q)) ∂cylinderMeasure) =
      ∫ q : ℍ × ℍ, A u w q * conj (A v s (lower q)) ∂cylinderMeasure := by
  let A : ℍ × ℍ → ℂ := fun q => SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF w) q.1 q.2
  let lower : ℍ × ℍ → ℍ × ℍ := if reverse then Prod.swap else id
  let B : ℍ × ℍ → ℂ := fun q =>
    SourceKernel.bilinear (μ ν P F hF v) (μ ν P F hF s) (lower q).1 (lower q).2
  let Ac : ℝ → ℍ × ℍ → ℂ := fun e q =>
    SourceKernel.invariantBilinear (μ ν P F hF u) (μ ν P F hF w) e q.1 q.2
  let Bc : ℝ → ℍ × ℍ → ℂ := fun t q =>
    SourceKernel.invariantBilinear (μ ν P F hF v) (μ ν P F hF s) t (lower q).1 (lower q).2
  let cylinderMeasure := (flatArea.restrict F).prod flatArea
  let W : ℍ × ℍ → ℝ := fun q => SourceKernel.absoluteCrossPair q.1 q.2
  have hA : MemLp A 2 cylinderMeasure := nativeWeilPetersson_bilinear_region_memLp_two
    R hp hg hgenus hΓ hfree hsmooth ν P F hF u w
  have hB : MemLp B 2 cylinderMeasure := by
    cases reverse with
    | false =>
        simpa only [B, lower, Bool.false_eq_true, ↓reduceIte, id_eq] using
          nativeWeilPetersson_bilinear_region_memLp_two R hp hg hgenus hΓ hfree hsmooth ν P F hF v s
    | true =>
        have hi := nativeWeilPetersson_bilinear_region_memLp_two
          R hp hg hgenus hΓ hfree hsmooth ν P F hF s v
        apply (memLp_congr_ae (g := B) ?_).mp hi
        exact Eventually.of_forall fun q => by
          simpa only [B, lower, ↓reduceIte, Prod.fst_swap, Prod.snd_swap] using
            (nativeWeilPetersson_bilinear_transpose
              R hp hg hgenus hΓ hfree hsmooth ν P F hF v s q.2 q.1).symm
  have hW : MemLp W 2 cylinderMeasure := SourceKernel.absoluteCrossPair_region_memLp_two
    (deformedNativeSurface R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) P F hF
  obtain ⟨Ca, hCa, hAm, hAb, hAlim⟩ := native_invariantBilinear_control
    R hp hg hgenus hΓ hfree hsmooth ν P F hF u w
  obtain ⟨Cb, hCb, hBrawm, hBrawb, hBrawlim⟩ := native_invariantBilinear_control
    R hp hg hgenus hΓ hfree hsmooth ν P F hF v s
  have hBm (t : ℝ) : StronglyMeasurable (Bc t) := by
    cases reverse with
    | false => simpa [Bc, lower] using hBrawm t
    | true =>
        simpa only [Bc, lower, ↓reduceIte, Function.comp_def, Prod.fst_swap, Prod.snd_swap] using
          (hBrawm t).comp_measurable measurable_swap
  have hBb (q : ℍ × ℍ) (t : ℝ) (ht0 : 0 < t) (ht16 : t < 1 / 16) :
      ‖Bc t q - B q‖ ≤ Cb * t * W q := by
    have hw : SourceKernel.absoluteCrossPair (lower q).1 (lower q).2 = W q := by
      cases reverse <;> simp only [lower, W, Bool.false_eq_true, ↓reduceIte, id_eq,
        Prod.fst_swap, Prod.snd_swap, SourceKernel.absoluteCrossPair_symm]
    calc
      _ ≤ Cb * t * SourceKernel.absoluteCrossPair (lower q).1 (lower q).2 :=
        hBrawb (lower q) t ht0 ht16
      _ = _ := by rw [hw]
  have hBlim (q : ℍ × ℍ) : Tendsto (fun t : ℝ => Bc t q) (𝓝[>] (0 : ℝ)) (𝓝 (B q)) :=
    hBrawlim (lower q)
  let U : ℍ × ℍ → ℝ := fun q => ‖A q‖ + Ca * W q
  let V : ℍ × ℍ → ℝ := fun q => ‖B q‖ + Cb * W q
  have hW0 (q : ℍ × ℍ) : 0 ≤ W q := SourceKernel.absoluteCrossPair_nonneg _ _
  have hU : MemLp U 2 cylinderMeasure := hA.norm.add (hW.const_mul Ca)
  have hV : MemLp V 2 cylinderMeasure := hB.norm.add (hW.const_mul Cb)
  have hU0 (q : ℍ × ℍ) : 0 ≤ U q := add_nonneg (norm_nonneg _) (mul_nonneg hCa (hW0 q))
  have hV0 (q : ℍ × ℍ) : 0 ≤ V q := add_nonneg (norm_nonneg _) (mul_nonneg hCb (hW0 q))
  have hnormA (e : ℝ) (he0 : 0 < e) (he16 : e < 1 / 16) (q : ℍ × ℍ) :
      ‖Ac e q‖ ≤ U q := by
    calc
      _ = ‖(Ac e q - A q) + A q‖ := by congr 1; ring
      _ ≤ ‖Ac e q - A q‖ + ‖A q‖ := norm_add_le _ _
      _ ≤ Ca * e * W q + ‖A q‖ :=
        _root_.add_le_add (hAb q e he0 he16) (le_refl ‖A q‖)
      _ ≤ _ := by
        have he1 : e ≤ 1 := by linarith
        have hmul := mul_le_mul_of_nonneg_right he1 (mul_nonneg hCa (hW0 q))
        dsimp only [U]
        nlinarith [hmul]
  have hnormB (t : ℝ) (ht0 : 0 < t) (ht16 : t < 1 / 16) (q : ℍ × ℍ) :
      ‖Bc t q‖ ≤ V q := by
    calc
      _ = ‖(Bc t q - B q) + B q‖ := by congr 1; ring
      _ ≤ ‖Bc t q - B q‖ + ‖B q‖ := norm_add_le _ _
      _ ≤ Cb * t * W q + ‖B q‖ :=
        _root_.add_le_add (hBb q t ht0 ht16) (le_refl ‖B q‖)
      _ ≤ _ := by
        have ht1 : t ≤ 1 := by linarith
        have hmul := mul_le_mul_of_nonneg_right ht1 (mul_nonneg hCb (hW0 q))
        dsimp only [V]
        nlinarith [hmul]
  have hAc (e : ℝ) (he0 : 0 < e) (he16 : e < 1 / 16) : MemLp (Ac e) 2 cylinderMeasure :=
    hU.mono' (hAm e).aestronglyMeasurable (Eventually.of_forall (hnormA e he0 he16))
  have hBc (t : ℝ) (ht0 : 0 < t) (ht16 : t < 1 / 16) : MemLp (Bc t) 2 cylinderMeasure :=
    hV.mono' (hBm t).aestronglyMeasurable (Eventually.of_forall (hnormB t ht0 ht16))
  have hdom : Integrable (fun q : ℍ × ℍ => U q * V q) cylinderMeasure := hU.integrable_mul hV
  have hfinite (e t : ℝ) (he0 : 0 < e) (he16 : e < 1 / 16) (ht0 : 0 < t)
      (ht16 : t < 1 / 16) : Integrable (fun q : ℍ × ℍ => Ac e q * conj (Bc t q)) cylinderMeasure :=
    (hAc e he0 he16).integrable_mul (show MemLp (fun q => conj (Bc t q)) 2 cylinderMeasure from (hBc t ht0 ht16).star)
  have hinner (e : ℝ) (he0 : 0 < e) (he16 : e < 1 / 16) :
      Integrable (fun q : ℍ × ℍ => Ac e q * conj (B q)) cylinderMeasure ∧
      Tendsto (fun t : ℝ => ∫ q : ℍ × ℍ, Ac e q * conj (Bc t q) ∂cylinderMeasure)
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ q : ℍ × ℍ, Ac e q * conj (B q) ∂cylinderMeasure)) := by
    refine ⟨(hAc e he0 he16).integrable_mul (show MemLp (fun q => conj (B q)) 2 cylinderMeasure from hB.star), ?_⟩
    apply tendsto_integral_filter_of_dominated_convergence (fun q : ℍ × ℍ => U q * V q)
    · exact Eventually.of_forall fun t => (hAm e).aestronglyMeasurable.mul (hBm t).aestronglyMeasurable.star
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 16)] with t ht
      exact Eventually.of_forall fun q => by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hnormA e he0 he16 q) (hnormB t ht.1 ht.2 q) (norm_nonneg _) (hU0 q)
    · exact hdom
    · exact Eventually.of_forall fun q =>
        tendsto_const_nhds.mul ((Complex.continuous_conj.tendsto _).comp (hBlim q))
  have houter : Tendsto (fun e : ℝ => ∫ q : ℍ × ℍ, Ac e q * conj (B q) ∂cylinderMeasure)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ q : ℍ × ℍ, A q * conj (B q) ∂cylinderMeasure)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun q : ℍ × ℍ => U q * V q)
    · exact Eventually.of_forall fun e => (hAm e).aestronglyMeasurable.mul hB.aestronglyMeasurable.star
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 16)] with e he
      exact Eventually.of_forall fun q => by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hnormA e he.1 he.2 q)
          (le_add_of_nonneg_right (mul_nonneg hCb (hW0 q))) (norm_nonneg _) (hU0 q)
    · exact hdom
    · exact Eventually.of_forall fun q => (hAlim q).mul_const (conj (B q))
  refine ⟨hfinite, hinner, houter, ?_⟩
  have heq : ∀ᶠ e in 𝓝[>] (0 : ℝ),
      (Filter.limUnder (𝓝[>] (0 : ℝ)) fun t : ℝ =>
        ∫ q : ℍ × ℍ, Ac e q * conj (Bc t q) ∂cylinderMeasure) =
        ∫ q : ℍ × ℍ, Ac e q * conj (B q) ∂cylinderMeasure := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 16)] with e he
    exact (hinner e he.1 he.2).2.limUnder_eq
  exact (houter.congr' (Filter.Eventually.mono heq fun _ h => h.symm)).limUnder_eq

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
