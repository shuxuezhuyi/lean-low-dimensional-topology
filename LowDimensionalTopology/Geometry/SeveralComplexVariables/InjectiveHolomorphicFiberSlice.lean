module

public import LowDimensionalTopology.Geometry.SeveralComplexVariables.ScalarPartialAnalyticChart
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Tactic.FunProp

/-!
# The actual lower-dimensional fiber slice

The scalar-partial chart is the actual chart of one original component.
Restrict its actual inverse to the fixed first coordinate. The remaining
original components are analytic and injective on an actual open ball;
only then is the lower-dimensional induction hypothesis applied.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.SeveralComplexVariables

/-- Restrict an injective analytic map to a fiber of its scalar-partial chart.
The induction premise concerns dimension m, while the map has dimension m+1. -/
theorem exists_injective_holomorphic_fiber_slice {m : ℕ}
    (ih : ∀ (V : Set (Fin m → ℂ)), IsOpen V → IsPreconnected V →
      ∀ (K : (Fin m → ℂ) → (Fin m → ℂ)), AnalyticOnNhd ℂ K V → Set.InjOn K V →
        ∀ w ∈ V, Function.Injective (fderiv ℂ K w))
    {D : Set ((Fin m → ℂ) × ℂ)} (hD : IsOpen D)
    {a : (Fin m → ℂ) × ℂ} (ha : a ∈ D)
    {F : ((Fin m → ℂ) × ℂ) → (ℂ × (Fin m → ℂ))}
    (hF : AnalyticOnNhd ℂ F D) (hInj : Set.InjOn F D)
    (hpartial : ((fderiv ℂ F a) (0, 1)).1 ≠ 0) :
    ∃ (e : OpenPartialHomeomorph ((Fin m → ℂ) × ℂ) (ℂ × (Fin m → ℂ)))
      (V : Set (Fin m → ℂ)),
      let K : (Fin m → ℂ) → (Fin m → ℂ) :=
        fun w => (F (e.symm ((F a).1, w))).2
      (e : ((Fin m → ℂ) × ℂ) → (ℂ × (Fin m → ℂ))) =
          (fun z => ((F z).1, z.1)) ∧
      a ∈ e.source ∧ e.source ⊆ D ∧ AnalyticAt ℂ e.symm (e a) ∧
      (∀ q ∈ e.target, (F (e.symm q)).1 = q.1 ∧ (e.symm q).1 = q.2) ∧
      IsOpen V ∧ IsPreconnected V ∧ a.1 ∈ V ∧
      (∀ w ∈ V, ((F a).1, w) ∈ e.target ∧
        AnalyticAt ℂ e.symm ((F a).1, w)) ∧
      AnalyticOnNhd ℂ K V ∧ Set.InjOn K V ∧ Function.Injective (fderiv ℂ K a.1) := by
  have hfirst : AnalyticOnNhd ℂ (fun z => (F z).1) D := by
    intro z hz
    exact ((ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)).analyticAt (F z)).comp (hF z hz)
  have hfdFirst : fderiv ℂ (fun z => (F z).1) a =
      (ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)).comp (fderiv ℂ F a) :=
    ((ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)).hasFDerivAt.comp a
      (hF a ha).differentiableAt.hasFDerivAt).fderiv
  have hpart : (fderiv ℂ (fun z => (F z).1) a) (0, 1) ≠ 0 := by
    rw [hfdFirst]
    exact hpartial
  obtain ⟨e, heFun, heMem, heSource, heInv, heCoords⟩ :=
    exists_scalar_partial_analytic_chart hD ha hfirst hpart
  let c : ℂ := (F a).1
  let b : Fin m → ℂ := a.1
  have hePoint : e a = (c, b) := congrFun heFun a
  let W : Set (Fin m → ℂ) :=
    (fun w => (c, w)) ⁻¹' (e.target ∩ {q | AnalyticAt ℂ e.symm q})
  have hline : Continuous (fun w : (Fin m → ℂ) => (c, w)) := by fun_prop
  have hW : IsOpen W :=
    (e.open_target.inter (isOpen_analyticAt ℂ e.symm)).preimage hline
  have hbW : b ∈ W := by
    change (c, b) ∈ e.target ∧ AnalyticAt ℂ e.symm (c, b)
    rw [← hePoint]
    exact ⟨e.map_source heMem, heInv⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hbW)
  let V : Set (Fin m → ℂ) := Metric.ball b r
  have hbV : b ∈ V := Metric.mem_ball_self hr
  have hV : IsOpen V := Metric.isOpen_ball
  have hVc : IsPreconnected V := (convex_ball b r).isPreconnected
  have htarget (w : Fin m → ℂ) (hw : w ∈ V) :
      (c, w) ∈ e.target ∧ AnalyticAt ℂ e.symm (c, w) := hball hw
  have hsource (w : Fin m → ℂ) (hw : w ∈ V) : e.symm (c, w) ∈ D :=
    heSource (e.map_target (htarget w hw).1)
  let K : (Fin m → ℂ) → (Fin m → ℂ) := fun w => (F (e.symm (c, w))).2
  have hKa : AnalyticOnNhd ℂ K V := by
    intro w hw
    have hq : AnalyticAt ℂ (fun x : (Fin m → ℂ) => (c, x)) w :=
      analyticAt_const.prod analyticAt_id
    have hH : AnalyticAt ℂ (fun x : (Fin m → ℂ) => e.symm (c, x)) w :=
      (htarget w hw).2.comp hq
    have hFH : AnalyticAt ℂ (fun x : (Fin m → ℂ) => F (e.symm (c, x))) w :=
      (hF (e.symm (c, w)) (hsource w hw)).comp
        (f := fun x : (Fin m → ℂ) => e.symm (c, x)) (x := w) hH
    exact ((ContinuousLinearMap.snd ℂ ℂ (Fin m → ℂ)).analyticAt
      (F (e.symm (c, w)))).comp
        (f := fun x : (Fin m → ℂ) => F (e.symm (c, x))) (x := w) hFH
  have hKi : Set.InjOn K V := by
    intro x hx y hy hxy
    have hFx : (F (e.symm (c, x))).1 = c := (heCoords (c, x) (htarget x hx).1).1
    have hFy : (F (e.symm (c, y))).1 = c := (heCoords (c, y) (htarget y hy).1).1
    have hwhole : F (e.symm (c, x)) = F (e.symm (c, y)) :=
      Prod.ext (hFx.trans hFy.symm) hxy
    have hHxy := hInj (hsource x hx) (hsource y hy) hwhole
    calc
      x = (e.symm (c, x)).1 := (heCoords (c, x) (htarget x hx).1).2.symm
      _ = (e.symm (c, y)).1 := congrArg Prod.fst hHxy
      _ = y := (heCoords (c, y) (htarget y hy).1).2
  have hDK : Function.Injective (fderiv ℂ K b) := ih V hV hVc K hKa hKi b hbV
  exact ⟨e, V, heFun, heMem, heSource, heInv, heCoords,
    hV, hVc, hbV, htarget, hKa, hKi, hDK⟩


/-- A nonzero scalar partial and derivative injectivity in dimension m
imply derivative injectivity for the map in dimension m+1. The first
coordinate derivative and the fiber derivative determine the needed
triangular linear map. -/
theorem fderiv_injective_of_first_partial_ne_zero {m : ℕ}
    (ih : ∀ (V : Set (Fin m → ℂ)), IsOpen V → IsPreconnected V →
      ∀ (K : (Fin m → ℂ) → (Fin m → ℂ)), AnalyticOnNhd ℂ K V → Set.InjOn K V →
        ∀ w ∈ V, Function.Injective (fderiv ℂ K w))
    {D : Set ((Fin m → ℂ) × ℂ)} (hD : IsOpen D)
    {a : (Fin m → ℂ) × ℂ} (ha : a ∈ D)
    {F : ((Fin m → ℂ) × ℂ) → (ℂ × (Fin m → ℂ))}
    (hF : AnalyticOnNhd ℂ F D) (hInj : Set.InjOn F D)
    (hpartial : ((fderiv ℂ F a) (0, 1)).1 ≠ 0) :
    Function.Injective (fderiv ℂ F a) := by
  obtain ⟨e, V, heFun, heMem, heSource, heInv, heCoords,
      _hV, _hVc, _hbV, _hVtarget, _hKa, _hKi, hDK⟩ :=
    exists_injective_holomorphic_fiber_slice ih hD ha hF hInj hpartial
  let c : ℂ := (F a).1
  let b : Fin m → ℂ := a.1
  let q₀ : ℂ × (Fin m → ℂ) := (c, b)
  let T : (ℂ × (Fin m → ℂ)) → (ℂ × (Fin m → ℂ)) := F ∘ e.symm
  let K : (Fin m → ℂ) → (Fin m → ℂ) := fun w => (F (e.symm (c, w))).2
  let A : (ℂ × (Fin m → ℂ)) →L[ℂ] (ℂ × (Fin m → ℂ)) := fderiv ℂ T q₀
  let B : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) := fderiv ℂ K b
  have hePoint : e a = q₀ := congrFun heFun a
  have hq₀ : q₀ ∈ e.target := hePoint ▸ e.map_source heMem
  have hHpoint : e.symm q₀ = a := by
    rw [← hePoint]
    exact e.left_inv heMem
  have hHdiff : DifferentiableAt ℂ e.symm q₀ := hePoint ▸ heInv.differentiableAt
  have hFatH : DifferentiableAt ℂ F (e.symm q₀) := by
    rw [hHpoint]
    exact (hF a ha).differentiableAt
  have hTdiff : DifferentiableAt ℂ T q₀ := hFatH.comp q₀ hHdiff
  have hFirstEq : (fun q => (T q).1) =ᶠ[𝓝 q₀] Prod.fst :=
    Filter.Eventually.mono
      (show ∀ᶠ q in 𝓝 q₀, q ∈ e.target from e.open_target.mem_nhds hq₀)
      fun q hq => (heCoords q hq).1
  have hFirstFD : HasFDerivAt (@Prod.fst ℂ (Fin m → ℂ))
      ((ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)).comp A) q₀ :=
    hTdiff.hasFDerivAt.fst.congr_of_eventuallyEq hFirstEq.symm
  have hFirstLinear : (ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)).comp A =
      ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ) := hFirstFD.unique hasFDerivAt_fst
  have hfirst (v : ℂ × (Fin m → ℂ)) : (A v).1 = v.1 :=
    congrArg (fun L : (ℂ × (Fin m → ℂ)) →L[ℂ] ℂ => L v) hFirstLinear
  have hslice : HasFDerivAt (fun w : (Fin m → ℂ) => (c, w))
      (ContinuousLinearMap.inr ℂ ℂ (Fin m → ℂ)) b :=
    hasFDerivAt_prodMk_right c b
  have hKFD : HasFDerivAt K
      ((ContinuousLinearMap.snd ℂ ℂ (Fin m → ℂ)).comp
        (A.comp (ContinuousLinearMap.inr ℂ ℂ (Fin m → ℂ)))) b :=
    (hTdiff.hasFDerivAt.comp b hslice).snd
  have hBLinear : B = (ContinuousLinearMap.snd ℂ ℂ (Fin m → ℂ)).comp
      (A.comp (ContinuousLinearMap.inr ℂ ℂ (Fin m → ℂ))) := hKFD.fderiv
  have hlower (w : Fin m → ℂ) : (A (0, w)).2 = B w :=
    (congrArg (fun L : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) => L w) hBLinear).symm
  have hBi : Function.Injective B := hDK
  have hAi : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).2
    intro v hv
    have hfst : v.1 = 0 := (hfirst v).symm.trans (congrArg Prod.fst hv)
    have hvsplit : v = (0, v.2) := Prod.ext hfst rfl
    have hBzero : B v.2 = 0 := by
      calc
        B v.2 = (A (0, v.2)).2 := (hlower v.2).symm
        _ = (A v).2 := congrArg (fun u => (A u).2) hvsplit.symm
        _ = 0 := congrArg Prod.snd hv
    have hsnd : v.2 = 0 := (injective_iff_map_eq_zero B).1 hBi v.2 hBzero
    exact Prod.ext hfst hsnd
  have hGdiff : DifferentiableAt ℂ e a := by
    rw [heFun]
    have hfirstA : AnalyticAt ℂ (fun z => (F z).1) a :=
      ((ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)).analyticAt (F a)).comp (hF a ha)
    exact (hfirstA.prod
      ((ContinuousLinearMap.fst ℂ (Fin m → ℂ) ℂ).analyticAt a)).differentiableAt
  have hHdiffImage : DifferentiableAt ℂ e.symm (e a) := by
    rw [hePoint]
    exact hHdiff
  have hLeftEq : e.symm ∘ e =ᶠ[𝓝 a] id :=
    Filter.Eventually.mono
      (show ∀ᶠ x in 𝓝 a, x ∈ e.source from e.open_source.mem_nhds heMem)
      fun x hx => e.left_inv hx
  have hLeftFD : HasFDerivAt (id : ((Fin m → ℂ) × ℂ) → ((Fin m → ℂ) × ℂ))
      ((fderiv ℂ e.symm q₀).comp (fderiv ℂ e a)) a := by
    have h := hHdiffImage.hasFDerivAt.comp a hGdiff.hasFDerivAt
    rw [hePoint] at h
    exact h.congr_of_eventuallyEq hLeftEq.symm
  have hRightInverse : (fderiv ℂ e.symm q₀).comp (fderiv ℂ e a) =
      ContinuousLinearMap.id ℂ ((Fin m → ℂ) × ℂ) :=
    hLeftFD.unique (hasFDerivAt_id a)
  have hHsurj : Function.Surjective (fderiv ℂ e.symm q₀) := by
    intro v
    refine ⟨(fderiv ℂ e a) v, ?_⟩
    exact congrArg (fun L : ((Fin m → ℂ) × ℂ) →L[ℂ] ((Fin m → ℂ) × ℂ) => L v)
      hRightInverse
  have hAcomp : A = (fderiv ℂ F a).comp (fderiv ℂ e.symm q₀) := by
    have h := fderiv_comp q₀ hFatH hHdiff
    rw [hHpoint] at h
    exact h
  intro v w hvw
  obtain ⟨x, hx⟩ := hHsurj v
  obtain ⟨y, hy⟩ := hHsurj w
  have hAx : A x = A y := by
    rw [hAcomp]
    change (fderiv ℂ F a) ((fderiv ℂ e.symm q₀) x) =
      (fderiv ℂ F a) ((fderiv ℂ e.symm q₀) y)
    rw [hx, hy]
    exact hvw
  have hxy : x = y := hAi hAx
  calc
    v = (fderiv ℂ e.symm q₀) x := hx.symm
    _ = (fderiv ℂ e.symm q₀) y := congrArg (fderiv ℂ e.symm q₀) hxy
    _ = w := hy

end LowDimensionalTopology.Geometry.SeveralComplexVariables
