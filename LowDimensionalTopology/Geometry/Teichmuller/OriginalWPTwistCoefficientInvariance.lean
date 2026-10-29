module

public import LowDimensionalTopology.Geometry.Teichmuller.WolpertLengthContractionCoordinates
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalWeilPeterssonFormCartan

/-!
# Original WP coefficient invariance from length duality and Cartan

The actual marked length supplies an exact contraction. Its second exterior
derivative vanishes by the existing normed-space theorem. The explicit
classical Cartan and evaluation identities then give the original scalar
coefficient derivative when the two required native brackets vanish.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "T" => TeichmullerSpace R
local notation "E" => Fin (3*g-3) → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "c" => nativeWeilPeterssonCoordinateChart
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "D" => nativeWeilPeterssonRealTangentCoordinateEquiv
  R hp hg hgenus hΓ hfree hsmooth
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "ωWP" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth
local notation "Along" => nativeWeilPeterssonFormLieDerivativeAlong
  R hp hg hgenus hΓ hfree hsmooth
local notation "lengthOf" => markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  (I := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth)

private theorem nativeWP_contraction_closed_of_lengthDuality
    (α : LiZhongQC.Loop X) (V : TopologicalSpace.Opens T) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (W : FormInterior.SmoothVectorField RI (M := T)),
      ContMDiffOn RI 𝓘(ℝ) ∞ (lengthOf α) (V : Set T) →
      (∀ q ∈ V, Unproved.Teichmuller.WolpertLengthDualityAt
        R hp hg hgenus hΓ hfree hsmooth q α (W q)) →
      ∀ q ∈ V,
        extDerivWithin
          (fun z : E => (Ω z).curryLeft (D ((c).symm z) (W ((c).symm z))))
          (c).target (c q) = 0 := by
  let := C
  let : IsManifold RI ω T := realManifold
  intro W hLength hDual q hq
  let H : E → ℝ := lengthOf α ∘ (c).symm
  let F₀ : E → E [⋀^Fin 0]→L[ℝ] ℝ :=
    fun z => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (H z)
  let η : E → E [⋀^Fin 1]→L[ℝ] ℝ :=
    fun z => (Ω z).curryLeft (D ((c).symm z) (W ((c).symm z)))
  have hsource : q ∈ (c).source := mem_chart_source E q
  have htarget : c q ∈ (c).target := (c).map_source hsource
  have hleft : (c).symm (c q) = q := (c).left_inv hsource
  have hinv : ContMDiffAt RI RI ∞ (c).symm (c q) := by
    have h := contMDiffOn_chart_symm (I := RI) (n := ∞) (x := basePoint R)
    change ContMDiffOn RI RI ∞ (c).symm (c).target at h
    exact h.contMDiffAt ((c).open_target.mem_nhds htarget)
  have hLengthAt : ContMDiffAt RI 𝓘(ℝ) ∞ (lengthOf α) ((c).symm (c q)) := by
    rw [hleft]
    exact (hLength q hq).contMDiffAt (V.isOpen.mem_nhds hq)
  have hH : ContDiffAt ℝ ∞ H (c q) := (hLengthAt.comp (c q) hinv).contDiffAt
  have hF₀ : ContDiffAt ℝ ∞ F₀ (c q) := by
    exact
      ((ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℝ (Fin 0)).contDiff.contDiffAt).comp
        (c q) hH
  have hpre : ∀ᶠ z : E in 𝓝 (c q), (c).symm z ∈ V := by
    apply hinv.continuousAt
    apply V.isOpen.mem_nhds
    rw [hleft]
    exact hq
  have heq : η =ᶠ[𝓝 (c q)] extDeriv F₀ := by
    filter_upwards [(c).open_target.mem_nhds htarget, hpre] with z hz hv
    let r := (c).symm z
    have hcr : c r = z := (c).right_inv hz
    have hLengthr : MDifferentiableAt RI 𝓘(ℝ) (lengthOf α) r :=
      ((hLength r hv).contMDiffAt (V.isOpen.mem_nhds hv)).mdifferentiableAt (by simp)
    have hc := nativeWP_contraction_coordinates_eq_lengthDeriv
      R hp hg hgenus hΓ hfree hsmooth α r (W r) hLengthr (hDual r hv)
    apply ContinuousAlternatingMap.ext
    intro v
    rw [extDeriv_constOfIsEmpty]
    change (Ω z).curryLeft (D r (W r)) v = fderiv ℝ H z (v 0)
    have h := hc (v 0)
    rw [hcr] at h
    convert h using 1
    congr 1
    funext i
    fin_cases i; rfl
  have hz : extDeriv η (c q) = 0 :=
    heq.extDeriv_eq.trans (extDeriv_extDeriv_apply hF₀ (by simp))
  simpa only [extDerivWithin, extDeriv,
    fderivWithin_of_isOpen (c).open_target htarget] using hz

/-- The original scalar WP coefficient has zero derivative along the given
length-dual flow when its two relevant native brackets vanish.

The closedness input comes from
`nativeWeilPeterssonCoordinateForm_closed_of_harmonicVariation`, with
local coefficient smoothness, harmonic naturality, the variation family
over the deformed references and the Eichler-jet input. Its target and
original coordinate form are unchanged. -/
theorem nativeWP_coefficient_twistDerivative_zero_of_lengthDuality
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (α : LiZhongQC.Loop X) (V : TopologicalSpace.Opens T)
    (ε : ℝ) (hε : 0 < ε) (Φ : ℝ → T → T) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (W Y Z : FormInterior.SmoothVectorField RI (M := T))
      (hzero : ∀ r ∈ V, Φ 0 r = r)
      (hflow : ∀ s ∈ Ioo (-ε) ε, ∀ t ∈ Ioo (-ε) ε,
        ∀ r ∈ V, s+t ∈ Ioo (-ε) ε → Φ t r ∈ V → Φ (s+t) r = Φ s (Φ t r))
      (hΦ : ContMDiffOn (𝓘(ℝ).prod RI) RI ∞
        (fun z : ℝ × T => Φ z.1 z.2) (Ioo (-ε) ε ×ˢ (V : Set T)))
      (hgen : ∀ t ∈ Ioo (-ε) ε, ∀ r ∈ V,
        mfderiv 𝓘(ℝ) RI (fun s : ℝ => Φ s r) t
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1) = W (Φ t r)),
    Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
      R hp hg hgenus hΓ hfree hsmooth hWP V ε hε Φ W Y Z hzero hflow hΦ hgen →
    ContMDiffOn RI 𝓘(ℝ) ∞ (lengthOf α) (V : Set T) →
    (∀ q ∈ V, Unproved.Teichmuller.WolpertLengthDualityAt
      R hp hg hgenus hΓ hfree hsmooth q α (W q)) →
    (∀ z ∈ (c).target, extDerivWithin Ω (c).target z = 0) →
    (∀ q ∈ V, VectorField.mlieBracket RI W Y q = 0) →
    (∀ q ∈ V, VectorField.mlieBracket RI W Z q = 0) →
    ∀ q ∈ V, mfderiv RI 𝓘(ℝ) (fun r => ωWP r ![Y r,Z r]) q (W q) = 0 := by
  let := C
  let : IsManifold RI ω T := realManifold
  intro W Y Z hzero hflow hΦ hgen hClassical hLength hDual hClosed hWY hWZ q hq
  rcases hClassical with ⟨hCartan, hEval⟩
  have hη := nativeWP_contraction_closed_of_lengthDuality
    R hp hg hgenus hΓ hfree hsmooth α V W hLength hDual q hq
  have ht : c q ∈ (c).target := (c).map_source (mem_chart_source E q)
  have hLie := hCartan q hq (Y q) (Z q)
  rw [hη, hClosed (c q) ht] at hLie
  have hLieZero : Along q V hq ε hε Φ W hzero hflow hΦ hgen ![Y q,Z q] = 0 := by
    simpa using hLie
  have hfirst : ωWP q ![VectorField.mlieBracket RI W Y q,Z q] = 0 := by
    rw [hWY q hq]
    exact (ωWP q).map_coord_zero (0 : Fin 2) rfl
  have hsecond : ωWP q ![Y q,VectorField.mlieBracket RI W Z q] = 0 := by
    rw [hWZ q hq]
    exact (ωWP q).map_coord_zero (1 : Fin 2) rfl
  have he := hEval q hq
  rw [hLieZero, hfirst, hsecond, sub_zero, sub_zero] at he
  exact he.symm

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
