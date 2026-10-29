module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonBookKahler
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCoordinateExpressions
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Tactic.Linarith

/-!
# Lower-slot symmetry of the original WP Christoffel expression

The same actual coordinate two-form is closed. Its real exterior derivative
on four constant triples gives the complex coefficient derivative identity.
Only the existing global Bers chart and the original raised coefficients are
used; no covariant derivative or curvature object is constructed here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3*g-3)
local notation "E" => I → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "H" => nativeWeilPeterssonLocalCoefficient
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "Dz" => nativeWeilPeterssonCoordinateDz (g := g)
local notation "G" => nativeWeilPeterssonChristoffelExpression
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

theorem coordinateClosedTwoForm_cyclic
    {form : E → E [⋀^Fin 2]→L[ℝ] ℝ} {t : E}
    (hd : DifferentiableAt ℝ form t) (hc : extDeriv form t = 0) (u v w : E) :
    fderiv ℝ form t u ![v,w] - fderiv ℝ form t v ![u,w] +
      fderiv ℝ form t w ![u,v] = 0 := by
  have h0 : (0 : Fin 3).removeNth ![u,v,w] = ![v,w] := by
    ext i
    fin_cases i <;> rfl
  have h1 : (1 : Fin 3).removeNth ![u,v,w] = ![u,w] := by
    ext i
    fin_cases i <;> rfl
  have h2 : (2 : Fin 3).removeNth ![u,v,w] = ![u,v] := by
    ext i
    fin_cases i <;> rfl
  have h := congrArg (fun A : E [⋀^Fin 3]→L[ℝ] ℝ => A ![u,v,w]) hc
  rw [extDeriv_apply hd] at h
  simpa [Fin.sum_univ_three, h0, h1, h2,
    fderiv_continuousAlternatingMap_apply_const_apply hd, sub_eq_add_neg] using h

private theorem wp_coordinateForm_J (u v t : E) :
    Ω t ![Complex.I • u,v] = -Ω t ![u,Complex.I • v] ∧
      Ω t ![Complex.I • u,Complex.I • v] = Ω t ![u,v] := by
  let := C
  let q := (chart (basePoint R)).symm t
  let : InnerProductSpace.Core ℂ (TangentSpace TI q) :=
    nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth q
  have hI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
  simp only [nativeWeilPeterssonCoordinateForm_complexFrame,
    nativeWeilPeterssonFundamentalForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousLinearEquiv.map_smul,
    InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ),
    InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ),
    hI]
  constructor <;> simp [Complex.mul_re, Complex.mul_im]

/-- Closedness of the actual coordinate form gives symmetry of the
holomorphic coefficient derivative slots. -/
theorem nativeWeilPeterssonCoefficientDz_symm_of_closed
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (t : E) (ht : t ∈ (chart (basePoint R)).target)
    (hclosed : extDerivWithin Ω (chart (basePoint R)).target t = 0)
    (k l q : I) : Dz (H k q) l t = Dz (H l q) k t := by
  have hd : DifferentiableAt ℝ Ω t :=
    ((contDiffOn_nativeWeilPeterssonFundamentalRealCoordinateForm_of_localSmoothness
      R hp hg hgenus hΓ hfree hsmooth hWP (basePoint R)).contDiffAt
        ((chart (basePoint R)).open_target.mem_nhds ht)).differentiableAt (by simp)
  have hc : extDeriv Ω t = 0 := by
    simpa only [extDerivWithin,
      fderivWithin_of_isOpen (chart (basePoint R)).open_target ht, extDeriv] using hclosed
  let D := fderiv ℝ Ω t
  let e : I → E := fun r => Pi.single r 1
  have cyclic (u v w : E) : D u ![v,w] - D v ![u,w] + D w ![u,v] = 0 :=
    coordinateClosedTwoForm_cyclic hd hc u v w
  have mixed (a u v : E) : D a ![Complex.I • u,v] = -D a ![u,Complex.I • v] := by
    have hf : (fun s : E => Ω s ![Complex.I • u,v]) =
        (fun s : E => -Ω s ![u,Complex.I • v]) :=
      funext fun s => (wp_coordinateForm_J R hp hg hgenus hΓ hfree hsmooth u v s).1
    have h := congrArg (fun f : E → ℝ => fderiv ℝ f t a) hf
    simpa only [fderiv_fun_neg, neg_apply,
      fderiv_continuousAlternatingMap_apply_const_apply hd] using h
  have both (a u v : E) : D a ![Complex.I • u,Complex.I • v] = D a ![u,v] := by
    have hf : (fun s : E => Ω s ![Complex.I • u,Complex.I • v]) =
        (fun s : E => Ω s ![u,v]) :=
      funext fun s => (wp_coordinateForm_J R hp hg hgenus hΓ hfree hsmooth u v s).2
    have h := congrArg (fun f : E → ℝ => fderiv ℝ f t a) hf
    simpa only [fderiv_continuousAlternatingMap_apply_const_apply hd] using h
  have derivative (r s : I) (a : E) :
      fderiv ℝ (H r s) t a =
        (-1 / 2 : ℂ) * (D a ![Complex.I • e r,e s] : ℂ) -
          (Complex.I / 2) * (D a ![e r,e s] : ℂ) := by
    have he (u v : E) := Complex.ofRealCLM.hasFDerivAt.comp t
      (hd.hasFDerivAt.continuousAlternatingMap_apply_const ![u,v])
    have hh := ((he (Complex.I • e r) (e s)).const_mul (-1 / 2 : ℂ)).sub
      ((he (e r) (e s)).const_mul (Complex.I / 2))
    have hh' := hh.congr_of_eventuallyEq (Eventually.of_forall fun x =>
      nativeWeilPeterssonLocalCoefficient_from_coordinateForm
        R hp hg hgenus hΓ hfree hsmooth r s x)
    have h := congrArg (fun L : E →L[ℝ] ℂ => L a) hh'.fderiv
    simpa only [sub_apply, smul_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
      ContinuousLinearMap.flipAlternating_apply_apply, smul_eq_mul] using h
  have hI (r : I) : Pi.single r Complex.I = Complex.I • e r := by
    ext i
    by_cases hi : i = r <;> simp [e, hi]
  have h1 := cyclic (e l) (Complex.I • e k) (e q)
  have h2 := cyclic (Complex.I • e l) (e k) (e q)
  have h3 := cyclic (Complex.I • e l) (Complex.I • e k) (e q)
  have h4 := cyclic (e l) (e k) (e q)
  have hm := mixed (e q) (e l) (e k)
  have hb := both (e q) (e l) (e k)
  dsimp only [e] at h1 h2 h3 h4 hm hb
  apply sub_eq_zero.mp
  apply Complex.ext <;>
    norm_num [nativeWeilPeterssonCoordinateDz, hI, derivative, e,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;>
    linarith [h1, h2, h3, h4, hm, hb]

/-- Closedness of the same original WP form forces the lower Christoffel
slots to agree in the genuine global Bers target. All four analytic inputs
are the already registered inputs of the accepted book Kähler theorem. -/
theorem nativeWeilPeterssonChristoffelExpression_lower_symm_of_harmonicVariation
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (hvariation : ∀ ν : Ball Γ, Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
      (deformedNativeSurface R hgenus hΓ hp ν)
      (deformedNativeSurface_uniformization R hgenus hΓ hp ν) hg
      (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) (deformedGroup_spec hΓ ν).1
      (deformedNativeSurface_actsFreely R hgenus hΓ hp ν) hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
    (j k l : I) (t : E) (ht : t ∈ (chart (basePoint R)).target) :
    G j k l t = G j l k t := by
  have hbook := nativeWeilPeterssonIsBookKahler_of_harmonicVariation
    R hp hg hgenus hΓ hfree hsmooth hWP hvariation hjets
  have hclosed : extDerivWithin Ω (chart (basePoint R)).target t = 0 :=
    hbook.2.2.2.2.2.2.2 t ht
  unfold nativeWeilPeterssonChristoffelExpression
  apply Finset.sum_congr rfl
  intro q _
  rw [nativeWeilPeterssonCoefficientDz_symm_of_closed
    R hp hg hgenus hΓ hfree hsmooth hWP t ht hclosed k l q]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
