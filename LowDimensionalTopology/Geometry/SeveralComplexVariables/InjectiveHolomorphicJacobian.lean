module

public import LowDimensionalTopology.Geometry.SeveralComplexVariables.FiniteComplexJacobian
public import LowDimensionalTopology.Geometry.SeveralComplexVariables.InjectiveHolomorphicCoordinates
public import LowDimensionalTopology.Geometry.SeveralComplexVariables.ZeroDerivativeOnZeroSet
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.Conformal
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Tactic.Order

/-!
# The Jacobian of an injective analytic map

The scalar case uses Wu Xiaobin's LiZhongQC univalence theorem
(Apache-2.0). In higher dimension, a scalar-partial coordinate chart gives
a lower-dimensional fiber. The geometric premise supplies a holomorphic
disk in a nonempty proper scalar analytic zero set.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.SeveralComplexVariables

/-- An injective analytic map in one complex dimension has injective
derivative, expressed in standard finite coordinates. -/
theorem fderiv_injective_of_injOn_fin_one
    {D : Set (Fin 1 → ℂ)} (hD : IsOpen D)
    {F : (Fin 1 → ℂ) → (Fin 1 → ℂ)} (hF : AnalyticOnNhd ℂ F D)
    (hInj : Set.InjOn F D) {a : Fin 1 → ℂ} (ha : a ∈ D) :
    Function.Injective (fderiv ℂ F a) := by
  let e : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  let U : Set ℂ := e.symm ⁻¹' D
  let G : ℂ → ℂ := e ∘ F ∘ e.symm
  let b : ℂ := e a
  have hea : e.symm b = a := e.symm_apply_apply a
  have hb : b ∈ U := by
    change e.symm b ∈ D
    rw [hea]
    exact ha
  have hU : IsOpen U := hD.preimage e.symm.continuous
  have hG : AnalyticOnNhd ℂ G U := by
    intro z hz
    exact ((e : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticAt (F (e.symm z))).comp
      (f := fun x : ℂ => F (e.symm x)) (x := z)
      ((hF (e.symm z) hz).comp ((e.symm : ℂ →L[ℂ] (Fin 1 → ℂ)).analyticAt z))
  have hGInj : Set.InjOn G U := by
    intro x hx y hy hxy
    exact e.symm.injective (hInj hx hy (e.injective hxy))
  have hGdiff : DifferentiableOn ℂ G U :=
    fun z hz => (hG z hz).differentiableAt.differentiableWithinAt
  have hderiv : deriv G b ≠ 0 := LiZhongQC.deriv_ne_zero_of_injOn hU hGdiff hGInj hb
  have hDGi : Function.Injective (fderiv ℂ G b) := by
    intro v w h
    simp only [fderiv_eq_deriv_mul] at h
    exact mul_right_injective₀ hderiv h
  have hGFD : HasFDerivAt G
      ((e : (Fin 1 → ℂ) →L[ℂ] ℂ).comp
        ((fderiv ℂ F (e.symm b)).comp (e.symm : ℂ →L[ℂ] (Fin 1 → ℂ)))) b :=
    (e : (Fin 1 → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp b
      ((hF (e.symm b) hb).differentiableAt.hasFDerivAt.comp b
        (e.symm : ℂ →L[ℂ] (Fin 1 → ℂ)).hasFDerivAt)
  have hGlinear : fderiv ℂ G b = (e : (Fin 1 → ℂ) →L[ℂ] ℂ).comp
      ((fderiv ℂ F a).comp (e.symm : ℂ →L[ℂ] (Fin 1 → ℂ))) := by
    have h := hGFD.fderiv
    rwa [hea] at h
  intro v w hvw
  apply e.injective
  apply hDGi
  rw [hGlinear]
  change e ((fderiv ℂ F a) (e.symm (e v))) =
    e ((fderiv ℂ F a) (e.symm (e w)))
  rw [e.symm_apply_apply, e.symm_apply_apply, hvw]

/-- An injective analytic map on a connected open subset of finite complex
space has injective derivative, assuming that nonempty proper scalar
analytic zero sets contain an injective holomorphic disk. -/
theorem fderiv_injective_of_injOn
    (hDisk : LowDimensionalTopology.Unproved.SeveralComplexVariables.HolomorphicZeroSetContainsDisk) :
    ∀ (n : ℕ), 1 ≤ n → ∀ (D : Set (Fin n → ℂ)), IsOpen D → IsPreconnected D →
      ∀ (F : (Fin n → ℂ) → (Fin n → ℂ)), AnalyticOnNhd ℂ F D → Set.InjOn F D →
        ∀ a ∈ D, Function.Injective (fderiv ℂ F a) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn D hD hDc F hF hInj a ha
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => exact fderiv_injective_of_injOn_fin_one hD hF hInj ha
      | succ k =>
        have ihLower : ∀ (V : Set (Fin (k + 1) → ℂ)), IsOpen V → IsPreconnected V →
            ∀ (K : (Fin (k + 1) → ℂ) → (Fin (k + 1) → ℂ)),
              AnalyticOnNhd ℂ K V → Set.InjOn K V →
                ∀ w ∈ V, Function.Injective (fderiv ℂ K w) := by
          intro V hV hVc K hK hKi w hw
          exact ih (k + 1) (Nat.lt_succ_self (k + 1)) (by omega) V hV hVc K hK hKi w hw
        have hDFcritical : ∀ z ∈ D, finiteComplexJacobian F z = 0 → fderiv ℂ F z = 0 := by
          intro z hz hJz
          by_contra hDF
          have hDi : Function.Injective (fderiv ℂ F z) :=
            fderiv_injective_of_fderiv_ne_zero ihLower hD hz hF hInj hDF
          exact ((finiteComplexJacobian_ne_zero_iff F z).2 hDi) hJz
        apply (finiteComplexJacobian_ne_zero_iff F a).1
        intro hJa
        have hproper : ∃ z ∈ D, finiteComplexJacobian F z ≠ 0 := by
          by_contra hnone
          have hDFall : D.EqOn (fderiv ℂ F) 0 := by
            intro z hz
            apply hDFcritical z hz
            by_contra hJz
            exact hnone ⟨z, hz, hJz⟩
          have hdiff : DifferentiableOn ℂ F D :=
            fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
          let : NeBot (𝓝[≠] a) := Module.punctured_nhds_neBot ℂ (Fin (k + 2) → ℂ) a
          have hDnear : ∀ᶠ z in 𝓝 a, z ∈ D := hD.mem_nhds ha
          have hev : ∀ᶠ z in 𝓝[≠] a, z ∈ D ∧ z ≠ a :=
            (hDnear.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
          obtain ⟨b, hb, hba⟩ := hev.exists
          have hFab : F b = F a := hD.is_const_of_fderiv_eq_zero
            (𝕜 := ℂ) (f := F) hDc hdiff hDFall hb ha
          exact hba (hInj hb ha hFab)
        exact not_injOn_of_fderiv_zero_on_zero_set hDisk (by omega) hD hDc
          (analyticOnNhd_finiteComplexJacobian hF) ⟨a, ha, hJa⟩ hproper hF hDFcritical hInj

/-- The standard-coordinate complex Jacobian of an injective analytic map
is nowhere zero, conditional on scalar zero-set disk existence. -/
theorem finiteComplexJacobian_ne_zero_of_injOn
    (hDisk : LowDimensionalTopology.Unproved.SeveralComplexVariables.HolomorphicZeroSetContainsDisk)
    {n : ℕ} (hn : 1 ≤ n) {D : Set (Fin n → ℂ)}
    (hD : IsOpen D) (hDc : IsPreconnected D)
    {F : (Fin n → ℂ) → (Fin n → ℂ)} (hF : AnalyticOnNhd ℂ F D)
    (hInj : Set.InjOn F D) {a : Fin n → ℂ} (ha : a ∈ D) :
    finiteComplexJacobian F a ≠ 0 :=
  (finiteComplexJacobian_ne_zero_iff F a).2
    (fderiv_injective_of_injOn hDisk n hn D hD hDc F hF hInj a ha)

end LowDimensionalTopology.Geometry.SeveralComplexVariables
