module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalWPBaseMixedHessian
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The actual coefficient Hessian on finite complex lines

The same smooth native coefficient restricts to its genuine complex line.
The full real chain rule identifies the mixed scalar Hessian with the finite
coordinate contraction, retaining both scalar complex directions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami

private theorem wp_realLinear_direction_expansion {n : ℕ}
    (L : (Fin n → ℂ) →L[ℝ] ℂ) (v : Fin n → ℂ) :
    L v = ∑ j,
      ((L (Pi.single j 1) - Complex.I * L (Pi.single j Complex.I)) / 2 * v j +
        (L (Pi.single j 1) + Complex.I * L (Pi.single j Complex.I)) / 2 * conj (v j)) := by
  classical
  have hv : v = ∑ j, Pi.single j (v j) := by ext j; simp
  calc
    L v = L (∑ j, Pi.single j (v j)) := congrArg L hv
    _ = ∑ j, L (Pi.single j (v j)) := map_sum L _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      let S : ℂ →L[ℝ] (Fin n → ℂ) :=
        ContinuousLinearMap.pi (Pi.single j (ContinuousLinearMap.id ℝ ℂ))
      let B : ℂ →L[ℝ] ℂ := L.comp S
      have hB (z : ℂ) : B z = L (Pi.single j z) := by
        change L (fun i => (Pi.single j (ContinuousLinearMap.id ℝ ℂ) :
          Fin n → ℂ →L[ℝ] ℂ) i z) = _
        congr 1
        ext i
        by_cases hij : i = j
        · subst i
          simp
        · simp [hij]
      have hd : fderiv ℝ B 0 = B := B.hasFDerivAt.fderiv
      have h := LiZhongQC.fderiv_eq_dz_dzbar (z₀ := (0 : ℂ))
        B.differentiableAt (v j)
      simpa only [LiZhongQC.dz, LiZhongQC.dzbar, hd, hB] using h

private theorem wp_complex_line_partials {g : ℕ}
    (f : (Fin (3 * g - 3) → ℂ) → ℂ) (v : Fin (3 * g - 3) → ℂ) (s : ℂ)
    (hf : DifferentiableAt ℝ f (s • v)) :
    (LiZhongQC.dz (fun z : ℂ => f (z • v)) s =
      ∑ j, nativeWeilPeterssonCoordinateDz f j (s • v) * v j) ∧
    (LiZhongQC.dzbar (fun z : ℂ => f (z • v)) s =
      ∑ j, nativeWeilPeterssonCoordinateDbar f j (s • v) * conj (v j)) := by
  classical
  have hd := hf.hasFDerivAt.comp s ((hasFDerivAt_id s).smul_const v)
  have hD (z : ℂ) : fderiv ℝ (fun a : ℂ => f (a • v)) s z =
      fderiv ℝ f (s • v) (z • v) := by
    have hd' := congrArg (fun A : ℂ →L[ℝ] ℂ => A z) hd.fderiv
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply] using hd'
  constructor
  · simp only [LiZhongQC.dz, hD, one_smul]
    rw [wp_realLinear_direction_expansion (fderiv ℝ f (s • v)) v,
      wp_realLinear_direction_expansion (fderiv ℝ f (s • v)) (Complex.I • v),
      Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I,
      nativeWeilPeterssonCoordinateDz]
    ring_nf; simp [Complex.I_sq]; ring
  · simp only [LiZhongQC.dzbar, hD, one_smul]
    rw [wp_realLinear_direction_expansion (fderiv ℝ f (s • v)) v,
      wp_realLinear_direction_expansion (fderiv ℝ f (s • v)) (Complex.I • v),
      Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I,
      nativeWeilPeterssonCoordinateDbar]
    ring_nf; simp [Complex.I_sq]; ring

private theorem wp_dz_sum_mul_const {n : ℕ} (f : Fin n → ℂ → ℂ) (c : Fin n → ℂ)
    (hf : ∀ j, DifferentiableAt ℝ (f j) 0) :
    LiZhongQC.dz (fun s => ∑ j, f j s * c j) 0 =
      ∑ j, LiZhongQC.dz (f j) 0 * c j := by
  classical
  have hD (j : Fin n) : fderiv ℝ (fun s => f j s * c j) 0 =
      c j • fderiv ℝ (f j) 0 := fderiv_mul_const (hf j) (c j)
  unfold LiZhongQC.dz
  simp only [fderiv_fun_sum (fun j _ => (hf j).mul_const (c j)),
    hD, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "U" => PartialEquiv.target (PartialHomeomorph.toPartialEquiv
  (OpenPartialHomeomorph.toPartialHomeomorph (chart (basePoint R))))
local notation "H" => nativeWeilPeterssonLocalCoefficient
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "Dz" => nativeWeilPeterssonCoordinateDz (g := g)
local notation "Dbar" => nativeWeilPeterssonCoordinateDbar (g := g)
local notation "C4" => nativeWeilPeterssonLoweredContraction
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

private theorem wp_line_origin_mem_target : (0 : E) ∈ U := by
  let := C
  have h := (chart (basePoint R)).map_source (mem_chart_source E (basePoint R))
  simpa only [nativeWeilPeterssonCoordinateChart_coe, bersCoordinates_basePoint] using h

/-- The mixed Hessian on the genuine scalar complex line is the finite
contraction of the original full coordinate mixed derivatives. -/
theorem nativeWeilPeterssonBaseCoefficient_line_mixedHessian
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) (j k : I) (v : E) :
    LiZhongQC.dz (fun s : ℂ => LiZhongQC.dzbar (fun z : ℂ => H j k (z • v)) s) 0 =
      ∑ l, ∑ m, Dz (fun t => Dbar (H j k) m t) l 0 * v l * conj (v m) := by
  classical
  have h0 := wp_line_origin_mem_target R hp hg hgenus hΓ hfree hsmooth
  have hF : ContDiffAt ℝ ∞ (H j k) 0 :=
    (hWP (basePoint R) j k).contDiffAt ((chart (basePoint R)).open_target.mem_nhds h0)
  have hdF : ContDiffAt ℝ 1 (fderiv ℝ (H j k)) 0 := hF.fderiv_right (by simp)
  have hDB (m : I) : DifferentiableAt ℝ (Dbar (H j k) m) 0 := by
    have h₁ := hdF.clm_apply (contDiffAt_const (c := (Pi.single m 1 : E)))
    have h₂ := hdF.clm_apply (contDiffAt_const (c := (Pi.single m Complex.I : E)))
    exact ((h₁.add (contDiffAt_const.mul h₂)).div_const (2 : ℂ)).differentiableAt (by simp)
  have hline : Continuous (fun s : ℂ => s • v) := continuous_id.smul continuous_const
  have hnear : ∀ᶠ s : ℂ in 𝓝 0, s • v ∈ U := by
    exact hline.continuousAt.preimage_mem_nhds
      ((chart (basePoint R)).open_target.mem_nhds (by simpa only [zero_smul] using h0))
  have hfirst : (fun s : ℂ => LiZhongQC.dzbar (fun z : ℂ => H j k (z • v)) s) =ᶠ[𝓝 0]
      (fun s => ∑ m, Dbar (H j k) m (s • v) * conj (v m)) := by
    filter_upwards [hnear] with s hs
    exact (wp_complex_line_partials (H j k) v s
      (((hWP (basePoint R) j k).contDiffAt
        ((chart (basePoint R)).open_target.mem_nhds hs)).differentiableAt (by simp))).2
  have hscalar (m : I) : DifferentiableAt ℝ (fun s : ℂ => Dbar (H j k) m (s • v)) 0 := by
    have hf : HasFDerivAt (Dbar (H j k) m) (fderiv ℝ (Dbar (H j k) m) 0)
        ((0 : ℂ) • v) := by
      simpa only [zero_smul] using (hDB m).hasFDerivAt
    exact (hf.comp 0 ((hasFDerivAt_id (0 : ℂ)).smul_const v)).differentiableAt
  calc
    _ = LiZhongQC.dz (fun s : ℂ => ∑ m, Dbar (H j k) m (s • v) * conj (v m)) 0 := by
      simp only [LiZhongQC.dz, hfirst.fderiv_eq]
    _ = ∑ m, LiZhongQC.dz (fun s : ℂ => Dbar (H j k) m (s • v)) 0 * conj (v m) :=
      wp_dz_sum_mul_const _ _ hscalar
    _ = ∑ m, ∑ l, Dz (fun t => Dbar (H j k) m t) l 0 * v l * conj (v m) := by
      apply Finset.sum_congr rfl
      intro m _
      have h := (wp_complex_line_partials (Dbar (H j k) m) v 0
        (by simpa only [zero_smul] using hDB m)).1
      rw [h]
      simp only [zero_smul, Finset.sum_mul]
    _ = _ := Finset.sum_comm

/-- The original lowered contraction with equal last directions is the
finite contraction of those actual scalar line Hessians. -/
theorem nativeWeilPeterssonBaseLoweredContraction_eq_line_mixedHessians
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (hvariation : Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0}) (u v w : E) :
    C4 u v w w 0 = ∑ j, ∑ k, u j * conj (v k) *
      LiZhongQC.dz (fun s : ℂ => LiZhongQC.dzbar (fun z : ℂ => H j k (z • w)) s) 0 := by
  rw [nativeWeilPeterssonBaseLoweredContraction_eq_actual_mixedHessianSum
    R hp hg hgenus hΓ hfree hsmooth hWP hvariation hjets]
  simp_rw [nativeWeilPeterssonBaseCoefficient_line_mixedHessian
    R hp hg hgenus hΓ hfree hsmooth hWP]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
