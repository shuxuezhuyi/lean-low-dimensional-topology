module

public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceWPAllPoints
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonRealCoefficients
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic.Ring

/-!
# The actual native coefficient matrix under inverse reference change

The genuine analytic inverse transports the same original Hermitian tensor.
Its finite coefficient formula transfers local smoothness from the fixed
original surface to the actual deformed reference, without a second input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "H" => nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "U" => PartialEquiv.target (PartialHomeomorph.toPartialEquiv
  (OpenPartialHomeomorph.toPartialHomeomorph (chart (basePoint R))))
local notation "coeff" => nativeWeilPeterssonLocalCoefficient R hp hg hgenus hΓ hfree hsmooth

private theorem reference_hermitian_sum
    (a : TeichmullerSpace.{0,0} R) (t u v : E) :
    letI := C
    let b := (chart a).symm t
    (H b).inner ((K b).symm v) ((K b).symm u) =
      ∑ j, ∑ k, u j * conj (v k) * coeff a j k t := by
  classical
  let := C
  let b := (chart a).symm t
  let c := H b
  let L := K b
  let : InnerProductSpace.Core ℂ (TangentSpace TI b) := c
  have hleft (S : Finset I) (f : I → TangentSpace TI b) (y : TangentSpace TI b) :
      c.inner (∑ i ∈ S, f i) y = ∑ i ∈ S, c.inner (f i) y := by
    let A : TangentSpace TI b →+ ℂ :=
      { toFun := fun x => c.inner x y
        map_zero' := InnerProductSpace.Core.inner_zero_left y
        map_add' := fun x z => c.add_left x z y }
    exact map_sum A f S
  have hright (S : Finset I) (f : I → TangentSpace TI b) (x : TangentSpace TI b) :
      c.inner x (∑ i ∈ S, f i) = ∑ i ∈ S, c.inner x (f i) := by
    calc
      _ = conj (c.inner (∑ i ∈ S, f i) x) := (c.conj_inner_symm x _).symm
      _ = conj (∑ i ∈ S, c.inner (f i) x) := congrArg conj (hleft S f x)
      _ = _ := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun i _ => c.conj_inner_symm x (f i))
  have hdecomp (z : E) : L.symm z = ∑ j, z j • L.symm (Pi.single j 1) := by
    calc
      _ = L.symm (∑ j, z j • Pi.single j 1) := congrArg L.symm (pi_eq_sum_univ' z)
      _ = _ := by simp only [map_sum, map_smul]
  change c.inner (L.symm v) (L.symm u) = _
  rw [hdecomp v, hdecomp u, hright]
  apply Finset.sum_congr rfl
  intro j _
  rw [hleft]
  apply Finset.sum_congr rfl
  intro k _
  rw [c.smul_left, InnerProductSpace.Core.inner_smul_right]
  change conj (v k) * (u j * c.inner
      (L.symm (Pi.single k 1)) (L.symm (Pi.single j 1))) =
    u j * conj (v k) * c.inner
      (L.symm (Pi.single k 1)) (L.symm (Pi.single j 1))
  ring

variable (ν : Ball Γ)

local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "hY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "Δ" => deformedGroup hΓ ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)
local notation "hfY" => deformedNativeSurface_actsFreely R hgenus hΓ hp ν
local notation "CY" => canonicalComplexChartedSpace Y hg hY hP hΔ hfY hpY hsmooth
local notation "BCY" => bersCoordinates Y hg hY hP hΔ hfY hpY
local notation "HY" => nativeWeilPeterssonCore Y hpY hg hY hΔ hfY hsmooth
local notation "KY" => nativeWeilPeterssonCoordinateEquiv Y hpY hg hY hΔ hfY hsmooth
local notation "chartY" => nativeWeilPeterssonCoordinateChart Y hpY hg hY hΔ hfY hsmooth
local notation "UY" => PartialEquiv.target (PartialHomeomorph.toPartialEquiv
  (OpenPartialHomeomorph.toPartialHomeomorph (chartY (basePoint Y))))
local notation "coeffY" => nativeWeilPeterssonLocalCoefficient Y hpY hg hY hΔ hfY hsmooth
local notation "A" => deformedReferenceChangeEquiv R hp hg hgenus hΓ ν
local notation "f" => deformedReferenceWeilPeterssonCoordinateMap R hp hg hgenus hΓ ν
local notation "q" => deformedReferenceWeilPeterssonInverseCoordinateMap R hp hg hgenus hΓ ν

private theorem reference_hermitian_pullback (t : E) (ht : t ∈ U) (u v : E) :
    (∑ j, ∑ k, u j * conj (v k) * coeff (basePoint R) j k t) =
      ∑ j, ∑ k, (fderiv ℝ f t u) j * conj ((fderiv ℝ f t v) k) *
        coeffY (basePoint Y) j k (f t) := by
  let := C
  let := CY
  rw [nativeWeilPeterssonCoordinateChart_target_eq_range] at ht
  obtain ⟨a, rfl⟩ := ht
  have hleft : (chart (basePoint R)).symm (BC a) = a := by
    simpa only [nativeWeilPeterssonCoordinateChart_coe] using
      (chart (basePoint R)).left_inv (mem_chart_source E a)
  have hleftY : (chartY (basePoint Y)).symm (f (BC a)) = A a := by
    rw [deformedReferenceWeilPeterssonCoordinateMap_point]
    simpa only [nativeWeilPeterssonCoordinateChart_coe] using
      (chartY (basePoint Y)).left_inv (mem_chart_source E (A a))
  have hframe (z : E) : mfderiv TI TI A a ((K a).symm z) =
      (KY (A a)).symm (fderiv ℝ f (BC a) z) := by
    apply (KY (A a)).injective
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      deformedReferenceWeilPeterssonCoordinateMap_tangent
        R hp hg hgenus hΓ hfree hsmooth ν a ((K a).symm z)
  have hR := reference_hermitian_sum R hp hg hgenus hΓ hfree hsmooth
    (basePoint R) (BC a) u v
  have hT := reference_hermitian_sum Y hpY hg hY hΔ hfY hsmooth
    (basePoint Y) (f (BC a)) (fderiv ℝ f (BC a) u) (fderiv ℝ f (BC a) v)
  dsimp only at hR hT
  rw [hleft] at hR
  rw [hleftY] at hT
  calc
    _ = (H a).inner ((K a).symm v) ((K a).symm u) := hR.symm
    _ = (HY (A a)).inner (mfderiv TI TI A a ((K a).symm v))
        (mfderiv TI TI A a ((K a).symm u)) :=
      (nativeWeilPeterssonCore_deformedReference_allPoints_pullback
        R hp hg hgenus hΓ hfree hsmooth ν a ((K a).symm u) ((K a).symm v)).symm
    _ = _ := by rw [hframe, hframe]; exact hT

include hfree hsmooth in
private theorem reference_inverse_derivative (y : E) (hy : y ∈ UY) :
    (fderiv ℝ f (q y)).comp (fderiv ℝ q y) = ContinuousLinearMap.id ℝ E := by
  have ha := deformedReferenceWeilPeterssonCoordinateMap_analytic
    R hp hg hgenus hΓ hfree hsmooth ν
  obtain ⟨_, hqU, _, hfq⟩ := deformedReferenceWeilPeterssonCoordinateMap_domains
    R hp hg hgenus hΓ hfree hsmooth ν
  have hevent : (fun z => f (q z)) =ᶠ[𝓝 y] id := by
    filter_upwards [(chartY (basePoint Y)).open_target.mem_nhds hy] with z hz
    exact hfq z hz
  have h := hevent.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp y ((ha.1 _ (hqU hy)).differentiableAt.restrictScalars ℝ)
    ((ha.2 _ hy).differentiableAt.restrictScalars ℝ), fderiv_id] at h
  exact h

/-- The same deformed native coefficient is the finite pullback by the
actual inverse-reference Jacobian, in the original first-linear convention. -/
theorem nativeWeilPeterssonDeformedCoefficient_eq_inverse_reference_sum
    (y : E) (hy : y ∈ UY) (j k : I) :
    coeffY (basePoint Y) j k y =
      ∑ a, ∑ b, (fderiv ℝ q y (Pi.single j 1)) a *
        conj ((fderiv ℝ q y (Pi.single k 1)) b) * coeff (basePoint R) a b (q y) := by
  let := C
  let := CY
  obtain ⟨_, hqU, _, hfq⟩ := deformedReferenceWeilPeterssonCoordinateMap_domains
    R hp hg hgenus hΓ hfree hsmooth ν
  have hD := reference_inverse_derivative R hp hg hgenus hΓ hfree hsmooth ν y hy
  have hDv (v : E) : fderiv ℝ f (q y) (fderiv ℝ q y v) = v :=
    congrArg (fun L : E →L[ℝ] E => L v) hD
  have hpull := reference_hermitian_pullback R hp hg hgenus hΓ hfree hsmooth ν
    (q y) (hqU hy) (fderiv ℝ q y (Pi.single j 1)) (fderiv ℝ q y (Pi.single k 1))
  rw [hfq y hy, hDv, hDv] at hpull
  have hb : coeffY (basePoint Y) j k y =
      ∑ a, ∑ b, (Pi.single j (1 : ℂ) : E) a *
        conj ((Pi.single k (1 : ℂ) : E) b) * coeffY (basePoint Y) a b y :=
    reference_hermitian_sum Y hpY hg hY hΔ hfY hsmooth
      (basePoint Y) y (Pi.single j 1) (Pi.single k 1)
  exact hb.trans hpull.symm

/-- Local smoothness of the fixed original matrix transports to the same
actual deformed reference through its established analytic inverse. -/
theorem nativeWeilPeterssonLocalCoefficientSmoothness_deformedReference
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      Y hpY hg hY hΔ hfY hsmooth := by
  intro a j k
  change ContDiffOn ℝ ∞ (coeffY (basePoint Y) j k) UY
  apply (chartY (basePoint Y)).open_target.contDiffOn_iff.mpr
  intro y hy
  have ha := deformedReferenceWeilPeterssonCoordinateMap_analytic
    R hp hg hgenus hΓ hfree hsmooth ν
  have hqU := (deformedReferenceWeilPeterssonCoordinateMap_domains
    R hp hg hgenus hΓ hfree hsmooth ν).2.1
  have hq : ContDiffAt ℝ ∞ q y := (ha.2 y hy).restrictScalars.contDiffAt
  have hdq : ContDiffAt ℝ ∞ (fderiv ℝ q) y := hq.fderiv_right (by simp)
  have hentry (c r : I) :
      ContDiffAt ℝ ∞ (fun x => (fderiv ℝ q x (Pi.single c 1)) r) y := by
    have hv : ContDiffAt ℝ ∞ (fun x => fderiv ℝ q x (Pi.single c 1)) y :=
      hdq.clm_apply contDiffAt_const
    exact contDiffAt_pi.mp hv r
  have hc (c r : I) :
      ContDiffAt ℝ ∞ (fun x => coeff (basePoint R) c r (q x)) y :=
    ((hWP (basePoint R) c r).contDiffAt
      ((chart (basePoint R)).open_target.mem_nhds (hqU hy))).comp y hq
  have hsum : ContDiffAt ℝ ∞
      (fun x => ∑ c, ∑ r, (fderiv ℝ q x (Pi.single j 1)) c *
        conj ((fderiv ℝ q x (Pi.single k 1)) r) * coeff (basePoint R) c r (q x)) y := by
    exact ContDiffAt.sum fun c _ => ContDiffAt.sum fun r _ =>
      ((hentry j c).mul (Complex.conjCLE.contDiff.comp_contDiffAt y (hentry k r))).mul (hc c r)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [(chartY (basePoint Y)).open_target.mem_nhds hy] with x hx
  exact nativeWeilPeterssonDeformedCoefficient_eq_inverse_reference_sum
    R hp hg hgenus hΓ hfree hsmooth ν x hx j k

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
