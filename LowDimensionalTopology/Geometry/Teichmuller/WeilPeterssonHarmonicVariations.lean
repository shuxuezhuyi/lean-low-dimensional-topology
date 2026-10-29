module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonLocalCoefficients
public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicAhlforsWeill
public import LowDimensionalTopology.Geometry.Teichmuller.HarmonicHyperbolicDensityVariation

/-!
# The actual harmonic Bers frame and source WP variation kernels

The frame is chosen from the literal Ahlfors--Weill section, with its full
coefficient-class identity retained. All planar integrals use Euclidean area.
No WP coefficient derivative is assumed in this module.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff BigOperators

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami HarmonicFirstVariation QuadraticBergman LiZhongQC

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : IsFuchsian Γ)

local notation "I" => Fin (3*g-3)
local notation "E" => I → ℂ
local notation "L" => weightedLinearBersCoordinates R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hp

include R hp hg hgenus hΓ

/-- The true inverse-coordinate section coefficients are literal original
harmonic coefficients. The factor -2 is absorbed in the quadratic frame. -/
theorem exists_nativeWeilPeterssonHarmonicFrame :
    ∃ q : I → HolomorphicQuadraticDifferential R.toRiemannAtlas,
      ∀ j, NativeHarmonicBeltrami.ofQuadratic R p hp (q j) =
        BersWeighted.ahlforsWeill ((L).symm (Pi.single j 1)) := by
  classical
  have h (j : I) := BersWeighted.exists_ahlforsWeill_eq_smul_ofQuadratic
    R p hp ((L).symm (Pi.single j 1))
  refine ⟨fun j => (-2 : ℂ) • Classical.choose (h j), ?_⟩
  intro j
  rw [NativeHarmonicBeltrami.ofQuadratic_smul]
  simpa only [map_neg, map_ofNat] using (Classical.choose_spec (h j)).symm

/-- A chosen original harmonic frame, retaining the exact section identity. -/
def nativeWeilPeterssonHarmonicFrame :
    I → HolomorphicQuadraticDifferential R.toRiemannAtlas :=
  Classical.choose (exists_nativeWeilPeterssonHarmonicFrame R hp hg hgenus hΓ)

theorem nativeWeilPeterssonHarmonicFrame_section (j : I) :
    NativeHarmonicBeltrami.ofQuadratic R p hp
      (nativeWeilPeterssonHarmonicFrame R hp hg hgenus hΓ j) =
      BersWeighted.ahlforsWeill ((L).symm (Pi.single j 1)) :=
  Classical.choose_spec (exists_nativeWeilPeterssonHarmonicFrame R hp hg hgenus hΓ) j

local notation "q" => nativeWeilPeterssonHarmonicFrame R hp hg hgenus hΓ

/-- The entire finite harmonic family is the same literal linear section. -/
theorem nativeWeilPeterssonHarmonicFrame_sum (t : E) :
    (∑ j, t j • NativeHarmonicBeltrami.ofQuadratic R p hp (q j)) =
      BersWeighted.ahlforsWeill ((L).symm t) := by
  classical
  calc
    (∑ j, t j • NativeHarmonicBeltrami.ofQuadratic R p hp (q j)) =
        ∑ j, t j • BersWeighted.ahlforsWeill ((L).symm (Pi.single j 1)) := by
      simp only [nativeWeilPeterssonHarmonicFrame_section]
    _ = BersWeighted.ahlforsWeill ((L).symm (∑ j, t j • Pi.single j 1)) := by
      let A : E →L[ℂ] GammaMeasurableBeltrami.Space Γ := ContinuousLinearMap.comp
        (BersWeighted.ahlforsWeill (Γ := Γ)) ((L).symm).toContinuousLinearMap
      have hsum : A (∑ j, t j • Pi.single j 1) =
          ∑ j, t j • A (Pi.single j 1) := by
        calc
          _ = ∑ j, A (t j • Pi.single j 1) :=
            map_sum A.toLinearMap.toAddMonoidHom
              (fun j : I => t j • Pi.single j 1) Finset.univ
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j _
            exact ContinuousLinearMap.map_smul A (t j) (Pi.single j 1)
      exact hsum.symm
    _ = BersWeighted.ahlforsWeill ((L).symm t) := by rw [← pi_eq_sum_univ' t]

/-- On the genuine small section ball the actual projected harmonic family
has exactly its original Bers coordinates, not only the same tangent map. -/
theorem nativeWeilPeterssonHarmonicFrame_coordinates
    (hfree : ActsFreely Γ) (t : E) (ht : ‖(L).symm t‖ < 1 / 2) :
    bersCoordinates R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
      (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
        (∑ j, t j • NativeHarmonicBeltrami.ofQuadratic R p hp (q j))) = t := by
  rw [nativeWeilPeterssonHarmonicFrame_sum, coefficientProjection_coordinates,
    BersWeighted.automorphicProjection_ahlforsWeill hΓ _ ht]
  exact (L).apply_symm_apply t

/-- The actual normalized symmetric-map kernel of source (7.38)--(7.41). -/
def nativeWeilPeterssonDeformationKernel (t : E) (z ζ : ℂ) : ℂ :=
  let f := coordinateFamily R p q t
  dz f z * dz f ζ / (f z - f ζ) ^ 2

/-- Source ψ_j, defined using the actual kernel and original harmonic function. -/
def nativeWeilPeterssonPulledQuadratic (j : I) (t : E) (z : ℍ) : ℂ :=
  (12 / (Real.pi : ℂ)) * ∫ ζ : ℂ in upperHalf,
    nativeWeilPeterssonDeformationKernel R hp hg hgenus hΓ t z (conj ζ) ^ 2 *
      conj (harmonicPlane R p (q j) ζ)

/-- The original lifted quadratic coefficient in this exact harmonic frame. -/
def nativeWeilPeterssonBaseQuadratic (j : I) (z : ℍ) : ℂ :=
  uniformizedQuadratic R p (q j) z

/-- The full real derivative of ψ_j along an actual complex coordinate axis. -/
def nativeWeilPeterssonPulledQuadraticVariation (j l : I) (a : ℂ) (z : ℍ) : ℂ :=
  fderiv ℝ (fun s : ℂ => nativeWeilPeterssonPulledQuadratic
    R hp hg hgenus hΓ j (Pi.single l s) z) 0 a

/-- The actual reciprocal-density term appearing in source (7.44). -/
def nativeWeilPeterssonDensityCorrection (F : Set ℍ) (j k l : I) (a : ℂ) : ℂ :=
  ∫ z in F, conj (nativeWeilPeterssonBaseQuadratic R hp hg hgenus hΓ j z) *
    nativeWeilPeterssonBaseQuadratic R hp hg hgenus hΓ k z *
      fderiv ℝ (fun s : ℂ =>
        ((coordinateDensity R p q (Pi.single l s) z)⁻¹ : ℂ)) 0 a ∂WeilPetersson.flatArea

/-- The reciprocal-density derivative vanishes along each harmonic coordinate axis. -/
theorem hasFDerivAt_nativeWeilPeterssonInverseDensity_zero
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0}) (l : I) (z : ℍ) :
    HasFDerivAt (fun s : ℂ =>
      ((coordinateDensity R p q (Pi.single l s) z)⁻¹ : ℂ))
      (0 : ℂ →L[ℝ] ℂ) 0 := by
  have h := hasFDerivAt_transportedHyperbolicDensity_zero R p hjets hp (q l) z
  have hv : transportedHyperbolicDensity R p (q l) 0 z = (z.im ^ 2)⁻¹ := by
    norm_num [transportedHyperbolicDensity, canonicalFamily_zero, jacobian, dz, dzbar,
      fderiv_id, div_eq_mul_inv]
  have hne : transportedHyperbolicDensity R p (q l) 0 z ≠ 0 := by
    rw [hv]
    exact inv_ne_zero (pow_ne_zero 2 z.im_pos.ne')
  have hi := (hasDerivAt_inv hne).hasFDerivAt.comp 0 h
  have hc := Complex.ofRealCLM.hasFDerivAt.comp 0 hi
  simpa only [coordinateDensity, coordinateFamily_axis, transportedHyperbolicDensity,
    ContinuousLinearMap.comp_zero, Function.comp_def, Complex.ofRealCLM_apply,
    Complex.ofReal_inv] using hc

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
