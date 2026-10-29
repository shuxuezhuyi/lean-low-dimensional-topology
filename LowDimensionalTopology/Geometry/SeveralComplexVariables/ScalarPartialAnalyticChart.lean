module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Inverse
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# The scalar-partial analytic coordinate chart

A nonzero scalar partial derivative produces the actual chart
z |-> (f z, z.1) on the original finite product. Its genuine inverse is
analytic at the original image point and preserves the remaining original
coordinates. The source is restricted inside the given original domain.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set

namespace LowDimensionalTopology.Geometry.SeveralComplexVariables

/-- The concrete local coordinate change determined by one nonzero original
scalar derivative entry. No whole vector-map Jacobian conclusion is a premise. -/
theorem exists_scalar_partial_analytic_chart {m : ℕ}
    {D : Set ((Fin m → ℂ) × ℂ)} (hD : IsOpen D)
    {a : (Fin m → ℂ) × ℂ} (ha : a ∈ D)
    {f : ((Fin m → ℂ) × ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f D)
    (hpartial : (fderiv ℂ f a) (0, 1) ≠ 0) :
    ∃ e : OpenPartialHomeomorph ((Fin m → ℂ) × ℂ) (ℂ × (Fin m → ℂ)),
      (e : ((Fin m → ℂ) × ℂ) → (ℂ × (Fin m → ℂ))) = (fun z => (f z, z.1)) ∧
      a ∈ e.source ∧ e.source ⊆ D ∧
      AnalyticAt ℂ e.symm (e a) ∧
      ∀ q ∈ e.target, f (e.symm q) = q.1 ∧ (e.symm q).1 = q.2 := by
  let P : ℂ →L[ℂ] ℂ :=
    (fderiv ℂ f a).comp (ContinuousLinearMap.inr ℂ (Fin m → ℂ) ℂ)
  have hP : P 1 ≠ 0 := hpartial
  let u : ℂˣ := Units.mk0 (P 1) hP
  let v : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ u
  have hv : (v : ℂ →L[ℂ] ℂ) = P := by
    apply ContinuousLinearMap.ext
    intro z
    change z * P 1 = P z
    simpa only [smul_eq_mul, mul_one] using (P.map_smul z (1 : ℂ)).symm
  have hPInv : P.IsInvertible := ⟨v, hv⟩
  let φ : ImplicitFunctionData ℂ ((Fin m → ℂ) × ℂ) ℂ (Fin m → ℂ) :=
    (hf a ha).hasStrictFDerivAt.implicitFunctionDataOfProdDomain hPInv
  let e₀ : OpenPartialHomeomorph ((Fin m → ℂ) × ℂ) (ℂ × (Fin m → ℂ)) :=
    φ.toOpenPartialHomeomorph
  have hφpt : φ.pt = a :=
    (hf a ha).hasStrictFDerivAt.pt_implicitFunctionDataOfProdDomain hPInv
  have hprod : φ.prodFun = (fun z => (f z, z.1)) := by
    funext z
    simp only [ImplicitFunctionData.prodFun_apply, φ,
      HasStrictFDerivAt.leftFun_implicitFunctionDataOfProdDomain,
      HasStrictFDerivAt.rightFun_implicitFunctionDataOfProdDomain]
  have he₀fun : (e₀ : ((Fin m → ℂ) × ℂ) → (ℂ × (Fin m → ℂ))) = φ.prodFun :=
    φ.toOpenPartialHomeomorph_coe
  have hmem : a ∈ e₀.source := by
    simpa only [hφpt] using φ.pt_mem_toOpenPartialHomeomorph_source
  have hG : AnalyticAt ℂ e₀ a := by
    rw [he₀fun, hprod]
    exact (hf a ha).prod ((ContinuousLinearMap.fst ℂ (Fin m → ℂ) ℂ).analyticAt a)
  obtain ⟨i, hi⟩ := φ.isInvertible_fderiv_prodFun
  have hi₀ : (i : ((Fin m → ℂ) × ℂ) →L[ℂ] (ℂ × (Fin m → ℂ))) =
      fderiv ℂ (e₀ : ((Fin m → ℂ) × ℂ) → (ℂ × (Fin m → ℂ))) a := by
    simpa only [he₀fun, hφpt] using hi
  obtain ⟨p, hp⟩ := hG
  have hcurry : continuousMultilinearCurryFin1 ℂ ((Fin m → ℂ) × ℂ)
      (ℂ × (Fin m → ℂ)) (p 1) =
      (i : ((Fin m → ℂ) × ℂ) →L[ℂ] (ℂ × (Fin m → ℂ))) :=
    hp.hasFDerivAt.fderiv.symm.trans hi₀.symm
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℂ
      ((Fin m → ℂ) × ℂ) (ℂ × (Fin m → ℂ))).symm
        (i : ((Fin m → ℂ) × ℂ) →L[ℂ] (ℂ × (Fin m → ℂ))) := by
    apply (continuousMultilinearCurryFin1 ℂ ((Fin m → ℂ) × ℂ)
      (ℂ × (Fin m → ℂ))).injective
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hcurry
  have hInv : AnalyticAt ℂ e₀.symm (e₀ a) :=
    (e₀.hasFPowerSeriesAt_symm (i := i) hmem hp hcoeff).analyticAt
  let e := e₀.restrOpen D hD
  have heFun : (e : ((Fin m → ℂ) × ℂ) → (ℂ × (Fin m → ℂ))) =
      (fun z => (f z, z.1)) := by
    change (e₀.restrOpen D hD : ((Fin m → ℂ) × ℂ) → (ℂ × (Fin m → ℂ))) = _
    rw [OpenPartialHomeomorph.coe_restrOpen, he₀fun, hprod]
  have heMem : a ∈ e.source := ⟨hmem, ha⟩
  have heSource : e.source ⊆ D := fun _ hz => hz.2
  have heInv : AnalyticAt ℂ e.symm (e a) := hInv
  refine ⟨e, heFun, heMem, heSource, heInv, ?_⟩
  intro q hq
  have heq := e.right_inv hq
  rw [heFun] at heq
  exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩

end LowDimensionalTopology.Geometry.SeveralComplexVariables
