/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNContinuousRealBranch
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Tactic.Ring

/-!
# Analyticity of the same continuous original real twist branch

The circle map retains the prescribed actual BV values at every marked
target. The geometric-family premise identifies its analytic complex phase.
A local rotated logarithm then gives an analytic germ of the same supplied
continuous real branch, in the original finite Fricke coordinates.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}

open Classical in
/-- Every chosen continuous real lift of the prescribed original circle
phases is real analytic on the entire original Fricke image. The actual
target-value equation and exact covering equation are retained. -/
theorem originalFNRealBranch_analyticOnNhd
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc)
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j) :
    ∀ j, AnalyticOnNhd ℝ
      (fun x : Fin (6 * g - 6) → ℝ =>
        if hx : x ∈ nativeFrickeImage hA then Θ ⟨x, hx⟩ j else 0)
      (nativeFrickeImage hA) := by
  classical
  rcases hU with ⟨A, hrep, _hchoices, hreg⟩
  have hφA (t : nativeFrickeImage hA) (j : Fin (3 * g - 3)) :
      φ t j = originalFNFamilyPhase hA hAlt D₀ A t j := by
    obtain ⟨p, hp⟩ := (mem_nativeFrickeImage_iff hA t.val).mp t.property
    obtain ⟨m, rfl⟩ := Quotient.exists_rep p
    have ht : t = ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ := Subtype.ext hp.symm
    rw [ht]
    exact (hφ m (chosenCanonicalModel hA m).model (A m).1 (A m).2 j).trans
      (originalFNFamilyPhase_coordinates hA hAlt D₀ A hrep m j).symm
  have hopen := (nativeFrickeImage_domain R hg hgenus hA hAlt).1
  intro j x₀ hx₀
  let t₀ : nativeFrickeImage hA := ⟨x₀, hx₀⟩
  let F : (Fin (6 * g - 6) → ℝ) → ℂ := fun x =>
    if hx : x ∈ nativeFrickeImage hA then (φ ⟨x, hx⟩ j : ℂ) else 0
  let T : (Fin (6 * g - 6) → ℝ) → ℝ := fun x =>
    if hx : x ∈ nativeFrickeImage hA then Θ ⟨x, hx⟩ j else 0
  have hF : AnalyticAt ℝ F x₀ := by
    apply (hreg j x₀ hx₀).congr
    filter_upwards [hopen.mem_nhds hx₀] with y hy
    simpa only [F, dite_eq_left hy] using
      congrArg (fun z : Circle => (z : ℂ)) (hφA ⟨y, hy⟩ j).symm
  have hTrest : Continuous ((nativeFrickeImage hA).domRestrict T) :=
    ((continuous_apply j).comp Θ.continuous).congr
      (fun t => by
        change Θ t j = T t.val
        exact (show T t.val = Θ t j from dite_eq_left t.property).symm)
  have hTOn : ContinuousOn T (nativeFrickeImage hA) :=
    continuousOn_iff_continuous_domRestrict.mpr hTrest
  have hTAt : ContinuousAt T x₀ := hTOn.continuousAt (hopen.mem_nhds hx₀)
  have hT₀ : T x₀ = Θ t₀ j := dite_eq_left hx₀
  let G : (Fin (6 * g - 6) → ℝ) → ℂ := fun x => F x / (φ t₀ j : ℂ)
  have hG : AnalyticAt ℝ G x₀ := hF.div_const
  have hG₀ : G x₀ = 1 := by
    simp only [G, F, dite_eq_left hx₀]
    exact div_self (Circle.coe_ne_zero (φ t₀ j))
  have hslit : G x₀ ∈ Complex.slitPlane := by
    rw [hG₀]
    exact Or.inl zero_lt_one
  have hlog : AnalyticAt ℝ (fun x => Complex.log (G x)) x₀ :=
    (show AnalyticAt ℝ Complex.log (G x₀) from
      (analyticAt_clog hslit).restrictScalars).comp hG
  let H : (Fin (6 * g - 6) → ℝ) → ℝ :=
    fun x => Θ t₀ j + (Complex.log (G x)).im
  have hH : AnalyticAt ℝ H x₀ :=
    analyticAt_const.add ((Complex.imCLM.analyticAt _).comp hlog)
  have hδ : ContinuousAt (fun x => T x - Θ t₀ j) x₀ :=
    hTAt.sub continuousAt_const
  have hδ₀ : T x₀ - Θ t₀ j = 0 := by rw [hT₀, sub_self]
  have hnear : ∀ᶠ x in 𝓝 x₀, T x - Θ t₀ j ∈ Ioo (-Real.pi) Real.pi := by
    apply hδ.eventually_mem
    rw [hδ₀]
    exact isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩
  change AnalyticAt ℝ T x₀
  apply hH.congr
  filter_upwards [hopen.mem_nhds hx₀, hnear] with y hy hangle
  let t : nativeFrickeImage hA := ⟨y, hy⟩
  have hTy : T y = Θ t j := dite_eq_left hy
  have hθt : Circle.exp (Θ t j) = φ t j := congrFun (hΘ j) t
  have hθ₀ : Circle.exp (Θ t₀ j) = φ t₀ j := congrFun (hΘ j) t₀
  have hphase : G y = (Circle.exp (Θ t j - Θ t₀ j) : ℂ) := by
    change F y / (φ t₀ j : ℂ) = (Circle.exp (Θ t j - Θ t₀ j) : ℂ)
    rw [show F y = (φ t j : ℂ) from dite_eq_left hy, ← Circle.coe_div,
      ← hθt, ← hθ₀, ← Circle.exp_sub]
  have hlogeq : Complex.log (G y) = ((T y - Θ t₀ j : ℝ) : ℂ) * Complex.I := by
    rw [hphase, Circle.coe_exp, ← hTy]
    apply Complex.log_exp
    · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero] using hangle.1
    · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero] using hangle.2.le
  have him : (Complex.log (G y)).im = T y - Θ t₀ j := by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero] using
      congrArg Complex.im hlogeq
  change Θ t₀ j + (Complex.log (G y)).im = T y
  rw [him]
  ring

end LowDimensionalTopology.Geometry.Teichmuller
