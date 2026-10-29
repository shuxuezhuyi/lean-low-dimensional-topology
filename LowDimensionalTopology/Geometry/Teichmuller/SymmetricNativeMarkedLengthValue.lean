module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientProjection
public import LowDimensionalTopology.Geometry.Teichmuller.MarkedGeodesicLength
public import LowDimensionalTopology.Geometry.Teichmuller.SourceMobiusAction
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.CoveredLoops
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalRegions
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The actual marked-length germ of the same symmetric coefficient curve

The original covering matrix is retained, including its possible negative
representative and its full traversal period. The native marked quotient's
length agrees near zero with the logarithm of the same normalized symmetric
map at the positive dilation. Only real boundary values of normalized lifts
are identified; no coefficient equality for a chosen smooth marking is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces LiZhongQC TeichmullerSpace

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable (hPresentation : Unproved.HandleGroupPresentation g)
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
variable (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
variable {p : ℍ → X}
variable (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
variable (α : LiZhongQC.Loop X)
variable (A0 : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA0 : A0 ∈ Γ)
variable (hcov : Covers p A0 α) (s : ℝ) (hs : 0 < s)
variable (hproj : Hyperbolic.realSLMobius A0 =
  Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))

include hA0 hcov hs hproj in
private theorem coefficientProjectionBall_length_eq_symmetric_log
    (ν : GammaMeasurableBeltrami.Ball Γ) :
    markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α
      (coefficientProjectionBall R hg hgenus hPresentation hΓ hfree hp ν) =
    Real.log ((s27u_fSym (GammaMeasurableBeltrami.planeRepresentative ν.val.val)
      (Real.exp (2 * s) : ℂ)).re) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let lam := Real.exp (2 * s)
  have hlam : 1 < lam := Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) hs)
  have hsource : mobiusSL (slRealToComplex A0) =
      mobiusSL (slRealToComplex (Fuchsian.hLogDilationSL s)) := by
    rw [← realSLMobius_source_action A0,
      ← realSLMobius_source_action (Fuchsian.hLogDilationSL s), hproj]
  have hAinf : mobiusSL (slRealToComplex A0) extInf = extInf := by
    rw [hsource]
    exact s27g_mob_infty.mpr (by simp [Fuchsian.hLogDilationSL])
  have hc0 : A0 1 0 = 0 := s27g_mob_infty.mp hAinf
  have hAzer : mobiusSL (slRealToComplex A0) (((0 : ℝ) : ℂ) : ExtPlane) =
      (((0 : ℝ) : ℂ) : ExtPlane) := by
    rw [hsource]
    exact s27g_mob_real_of
      (by simp [Fuchsian.hLogDilationSL])
      (by simp [Fuchsian.hLogDilationSL])
  have hb0 : A0 0 1 = 0 := by
    simpa only [mul_zero, zero_add, zero_mul] using (s27g_mob_real_eq hAzer).2
  have hexp : Real.exp s = lam * Real.exp (-s) := by
    dsimp only [lam]
    rw [← Real.exp_add]
    congr 1
    ring
  have hAone : mobiusSL (slRealToComplex A0) (((1 : ℝ) : ℂ) : ExtPlane) =
      ((lam : ℂ) : ExtPlane) := by
    rw [hsource]
    exact s27g_mob_real_of
      (by simp [Fuchsian.hLogDilationSL])
      (by simpa [Fuchsian.hLogDilationSL] using hexp)
  have hsq0 : A0 0 0 ^ 2 = lam := by
    have he := (s27g_mob_real_eq hAone).2
    have hd := hnf_sl2_det A0
    simp [hb0, hc0] at he hd
    linear_combination (A0 0 0) * he + lam * hd
  have hdiag0 : A0 0 1 = 0 ∧ A0 1 0 = 0 ∧ 1 < A0 0 0 ^ 2 :=
    ⟨hb0, hc0, by rwa [hsq0]⟩
  let P := coefficientProjectionBall R hg hgenus hPresentation hΓ hfree hp ν
  let m : MarkedRiemannSurface.{0, 0} R := Quotient.out P
  have hm : TeichmullerSpace.mk m = P := Quotient.out_eq P
  have hclass : sourceGammaEquiv R hg hgenus hPresentation hΓ hfree hp
      (Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma ν)) = Quot.mk _ m.toSource := by
    rw [← toSource_mk R m, hm]
    exact (toSource_coefficientProjectionBall R hg hgenus hPresentation hΓ hfree hp ν).symm
  have he := Classical.choose_spec (teichGamma_equiv_teichSpace hg
    (R.sourceHasGenus hgenus hPresentation) hΓ hfree hp)
  obtain ⟨Δ', q', F', G', hq', hN', hG'⟩ :=
    (he (GammaMeasurableBeltrami.toSourceGamma ν) m.toSource).mp hclass
  let := m.surface.toRiemannAtlas.toChartedSpace
  let := m.surface.toRiemannAtlas.isManifold
  let := m.surface.t2Space
  let := m.surface.connectedSpace
  let M := m.geodesicLengthModel R (Nat.succ_le_of_lt hg) hgenus
  obtain ⟨Δ, _, hM⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨B, F, G, hN⟩ := exists_normalizedLift hp hM m.toSource.marking m.toSource.qc
  have hMB := adjustProjection_isUniformization hM B
  have hboundary (x : ℝ) : G ((x : ℂ) : ExtPlane) =
      ((s27u_fSym (GammaMeasurableBeltrami.planeRepresentative ν.val.val) x : ℂ) : ExtPlane) := by
    have hh := (thm27_1 hg (R.sourceHasGenus hgenus hPresentation) hp m.toSource m.toSource
      hMB hq' hN hN').mp (markedRS_equiv_equivalence.refl m.toSource)
    simpa only [s33v_fSym_eq, GammaMeasurableBeltrami.toSourceGamma] using
      (hh x).trans (hG' x)
  obtain ⟨hLift, hExt, hG0, hG1, hGi⟩ := hN
  obtain ⟨bdy, hbdy, hmono, _, hbdy1⟩ := s27g_bdry_real hExt hG0 hG1 hGi
  obtain ⟨At, hAt, hrep⟩ := s27g_rep_exists hp hMB hLift hA0
  have hdiag := s27g_diag hExt hG0 hGi hbdy hmono hbdy1 hdiag0 hrep
  have hbdyLam : bdy lam =
      (s27u_fSym (GammaMeasurableBeltrami.planeRepresentative ν.val.val) (lam : ℂ)).re := by
    have heq := OnePoint.coe_injective ((hbdy lam).symm.trans (hboundary lam))
    simpa only [Complex.ofReal_re] using congrArg Complex.re heq
  have hsq : At 0 0 ^ 2 = bdy lam := by
    have hr := s27g_bdry_rel hExt hrep (s27t_mem_closure_real 1)
    simp only [Function.comp_apply] at hr
    rw [hAone, hbdy lam, hbdy 1, hbdy1] at hr
    have heq := (s27g_mob_real_eq hr.symm).2
    have hd := hnf_sl2_det At
    simp [hdiag.1, hdiag.2.1] at heq hd
    linear_combination (At 0 0) * heq + bdy lam * hd
  have hconj (z : ℍ) : F (A0 • z) = At • F z := by
    simpa only [F.symm_apply_apply] using (hrep (F z)).symm
  let β : LiZhongQC.Loop m.carrier := ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩
  have hcovt : Covers (adjustProjection M.halfPlaneCover B) At β := by
    obtain ⟨c, hcc, hcp, hc1⟩ := hcov
    refine ⟨fun t => F (c t), F.continuous.comp_continuousOn hcc, fun t ht => ?_, ?_⟩
    · rw [hLift, hcp t ht]
      show m.toSource.marking (α.2.extend t) = (α.2.map m.markingMap.continuous).extend t
      rw [Path.extend_apply _ ht, Path.extend_apply _ ht]
      rfl
    · show F (c 1) = At • F (c 0)
      rw [hc1, hconj]
  have hh : IsHyperbolic At := by
    have hd := (s27t_diag_facts hdiag).1
    have hne := (s27t_diag_facts hdiag).2.2
    have hp2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    have ht2 : 4 < (At 0 0 + At 1 1) ^ 2 := by nlinarith only [hd, hp2]
    change 2 < |At 0 0 + At 1 1|
    nlinarith only [ht2, sq_abs (At 0 0 + At 1 1), abs_nonneg (At 0 0 + At 1 1)]
  have hk : 0 < At 0 0 ^ 2 := zero_lt_one.trans hdiag.2.2
  have hscale : Hyperbolic.hSLIsometry At =
      Hyperbolic.hSLIsometry (Hyperbolic.verticalDilationSL (At 0 0 ^ 2) hk) := by
    apply IsometryEquiv.ext
    intro z
    apply UpperHalfPlane.ext
    change ((At • z : ℍ) : ℂ) =
      ((Hyperbolic.verticalDilationSL (At 0 0 ^ 2) hk • z : ℍ) : ℂ)
    rw [Hyperbolic.verticalDilationSL_coe, UpperHalfPlane.coe_specialLinearGroup_apply]
    have hd : (At 0 0 : ℂ) * (At 1 1 : ℂ) = 1 := by
      exact_mod_cast (s27t_diag_facts hdiag).1
    have hd0 : (At 1 1 : ℂ) ≠ 0 := right_ne_zero_of_mul_eq_one hd
    simp only [Algebra.algebraMap_self_apply, hdiag.1, hdiag.2.1,
      Complex.ofReal_zero, zero_mul, zero_add, add_zero]
    rw [div_eq_iff hd0]
    push_cast
    linear_combination -((At 0 0 : ℂ) * (z : ℂ)) * hd
  have htl : translationLength At = Real.log (At 0 0 ^ 2) := by
    rw [Hyperbolic.liZhong_translationLength_eq_native At hh, hscale,
      Hyperbolic.dilation_translationLength]
    exact abs_of_pos (Real.log_pos hdiag.2.2)
  have hlen : freeHomotopyLength (adjustProjection M.halfPlaneCover B) β =
      ENNReal.ofReal (Real.log (At 0 0 ^ 2)) := by
    rw [s30a_len_hyp hMB hAt hh hcovt, htl]
  have hcoverlen : freeHomotopyLength (adjustProjection M.halfPlaneCover B) β =
      freeHomotopyLength M.halfPlaneCover β := by
    have h := s30b_fhl_eq_of_mob
      (pX := M.halfPlaneCover) (pY := adjustProjection M.halfPlaneCover B)
      (Homeomorph.refl m.carrier) B (fun z => by
        change M.halfPlaneCover (B⁻¹ • (B • z)) = M.halfPlaneCover z
        rw [inv_smul_smul]) β
    change freeHomotopyLength (adjustProjection M.halfPlaneCover B)
      ⟨β.1, β.2.map continuous_id⟩ = freeHomotopyLength M.halfPlaneCover β at h
    simpa only [Path.map_id] using h
  change markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α P = _
  rw [← hm]
  change (freeHomotopyLength M.halfPlaneCover β).toReal = _
  rw [← hcoverlen, hlen, ENNReal.toReal_ofReal (Real.log_pos hdiag.2.2).le]
  rw [hsq, hbdyLam]

include hA0 hcov hs hproj in
/-- The actual marked-length function of the same native coefficient curve is
locally the logarithm of the original symmetric solution at the full dilation. -/
theorem marked_length_coefficient_curve_eventually_eq_symmetric_log
    (μ : GammaMeasurableBeltrami.Space Γ) :
    (fun t : ℝ =>
      markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α
        (coefficientProjection R hg hgenus hPresentation hΓ hfree hp ((t : ℂ) • μ)))
      =ᶠ[𝓝 0]
    (fun t : ℝ => Real.log ((s27u_fSym
      (GammaMeasurableBeltrami.planeRepresentative ((t : ℂ) • μ).val)
        (Real.exp (2 * s) : ℂ)).re)) := by
  classical
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ‖((t : ℂ) • μ)‖ < 1 :=
    (isOpen_lt ((Complex.continuous_ofReal.smul continuous_const).norm) continuous_const).mem_nhds
      (by
        simpa only [Set.mem_ofPred_eq, Pi.smul_apply', Complex.ofReal_zero, zero_smul,
          ZeroMemClass.coe_zero, norm_zero]
          using (zero_lt_one : (0 : ℝ) < 1))
  filter_upwards [hnear] with t ht
  let ν : GammaMeasurableBeltrami.Ball Γ :=
    ⟨(t : ℂ) • μ, by simpa only [Metric.mem_ball, dist_zero_right] using ht⟩
  have h := coefficientProjectionBall_length_eq_symmetric_log
    (R := R) (hg := hg) (hgenus := hgenus) (hPresentation := hPresentation)
    (hΓ := hΓ) (hfree := hfree) (hp := hp) (α := α)
    (A0 := A0) (hA0 := hA0) (hcov := hcov) (s := s) (hs := hs) (hproj := hproj) ν
  simpa only [coefficientProjection, dite_eq_left ht, ν] using h

end LowDimensionalTopology.Geometry.Teichmuller
