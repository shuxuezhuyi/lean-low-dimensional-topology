module

public import LowDimensionalTopology.Geometry.Teichmuller.PeterssonPairingMap
public import LowDimensionalTopology.Geometry.Teichmuller.BersAutomorphicDerivative
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# The actual Beltrami derivative quotient and the Petersson continuous dual

The infinitesimally trivial subspace is the kernel of the literal bounded Bers
integral operator, proved below to be the genuine Fréchet derivative kernel in
the bounded automorphic codomain. Its quotient carries the genuine L-infinity
quotient norm. The induced isomorphism evaluates to the book's actual pairing
on the original open fundamental region. Both directions are continuous by
the Banach inverse theorem; no assertion of isometry is made.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NativePetersson

open Surfaces WeilPetersson

/-- The actual infinitesimally trivial compatible Beltrami classes. -/
def infinitesimalSubmodule (Γ : Subgroup GammaMeasurableBeltrami.Deck) :
    Submodule ℂ (GammaMeasurableBeltrami.Space Γ) :=
  (BersWeighted.integralOperator Γ).ker

instance infinitesimalSubmodule_isClosed (Γ : Subgroup GammaMeasurableBeltrami.Deck) :
    IsClosed (infinitesimalSubmodule Γ : Set (GammaMeasurableBeltrami.Space Γ)) :=
  (BersWeighted.integralOperator Γ).isClosed_ker

/-- The genuine normed quotient of the original compatible L-infinity space. -/
abbrev TangentQuotient (Γ : Subgroup GammaMeasurableBeltrami.Deck) :=
  GammaMeasurableBeltrami.Space Γ ⧸ infinitesimalSubmodule Γ

/-- Its quotient norm is the norm induced by the actual L-infinity class norm. -/
theorem norm_tangentQuotient_mk_le {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (μ : GammaMeasurableBeltrami.Space Γ) :
    ‖(Submodule.Quotient.mk μ : TangentQuotient Γ)‖ ≤ ‖μ‖ :=
  Submodule.Quotient.norm_mk_le (infinitesimalSubmodule Γ) μ

/-- The subspace is precisely the derivative kernel in the original normed
bounded automorphic target, rather than only a pointwise variation kernel. -/
theorem mem_infinitesimalSubmodule_iff_fderiv
    {Γ : Subgroup GammaMeasurableBeltrami.Deck} (hΓ : LiZhongQC.IsFuchsian Γ)
    (μ : GammaMeasurableBeltrami.Space Γ) :
    μ ∈ infinitesimalSubmodule Γ ↔
      fderiv ℂ (BersWeighted.automorphicProjection hΓ) 0 μ = 0 := by
  rw [BersWeighted.fderiv_automorphicProjection hΓ]
  change BersWeighted.integralOperator Γ μ = 0 ↔
    BersWeighted.automorphicIntegralOperator hΓ μ = 0
  constructor
  · exact fun h => Subtype.ext h
  · exact fun h => congrArg Subtype.val h

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

local notation "Q" => Space R P p hp F hF
local notation "B" => GammaMeasurableBeltrami.Space Γ

/-- The native flat-area integral is exactly the book's original planar
integral, for the unchanged coefficient and original uniformizing lift. -/
theorem pairing_eq_planar (μ : B) (q : Q) :
    pairing R P p hp F hF μ q =
      ∫ z in UpperHalfPlane.coe '' F,
        GammaMeasurableBeltrami.planeRepresentative μ.val z *
          QuadraticBergman.uniformizedQuadratic R p
            (toQuadratic R P p hp F hF q) z := by
  have hsub : UpperHalfPlane.coe '' F ⊆ LiZhongQC.upperHalf := by
    rintro _ ⟨z, _, rfl⟩
    exact z.im_pos
  have he := UpperHalfPlane.measurableEmbedding_coe.setIntegral_map
    (μ := flatArea)
    (fun z => GammaMeasurableBeltrami.planeRepresentative μ.val z *
      QuadraticBergman.uniformizedQuadratic R p
        (toQuadratic R P p hp F hF q) z)
    (UpperHalfPlane.coe '' F)
  rw [GammaMeasurableBeltrami.map_flat_coe,
    Measure.restrict_restrict_of_subset hsub,
    UpperHalfPlane.coe_injective.preimage_image] at he
  unfold pairing
  rw [he]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp only [GammaMeasurableBeltrami.planeRepresentative_coe]
    rfl

/-- The literal dual-pairing map has precisely the genuine Bers derivative kernel. -/
theorem pairingMap_ker :
    (pairingMap R P p hp F hF).ker = infinitesimalSubmodule Γ := by
  ext μ
  change pairingMap R P p hp F hF μ = 0 ↔ BersWeighted.integralOperator Γ μ = 0
  have hk := BersWeighted.fderiv_projection_iff_nativeRegionAnnihilator R P p hp hF μ
  rw [BersWeighted.hasFDerivAt_projection.fderiv] at hk
  constructor
  · intro he
    apply hk.mpr
    intro q
    have hv := congrArg (fun f : StrongDual ℂ Q =>
      f ((toQuadratic R P p hp F hF).symm q)) he
    simpa only [pairingMap_apply, pairing_eq_planar, LinearEquiv.apply_symm_apply,
      zero_apply] using hv
  · intro he
    apply ContinuousLinearMap.ext
    intro q
    change pairing R P p hp F hF μ q = 0
    rw [pairing_eq_planar]
    exact hk.mp he (toQuadratic R P p hp F hF q)

/-- The actual pairing descends continuously to the actual derivative quotient. -/
def quotientPairing : TangentQuotient Γ →L[ℂ] StrongDual ℂ Q :=
  (infinitesimalSubmodule Γ).liftQL (pairingMap R P p hp F hF)
    (pairingMap_ker R P p hp F hF).symm.le

theorem quotientPairing_ker : (quotientPairing R P p hp F hF).ker = ⊥ := by
  exact Submodule.ker_liftQ_eq_bot (infinitesimalSubmodule Γ)
    (pairingMap R P p hp F hF).toLinearMap
    (pairingMap_ker R P p hp F hF).symm.le
    (pairingMap_ker R P p hp F hF).le

theorem quotientPairing_surjective :
    Function.Surjective (quotientPairing R P p hp F hF) := by
  intro f
  obtain ⟨μ, hμ⟩ := pairingMap_surjective R P p hp F hF f
  exact ⟨Submodule.Quotient.mk μ, hμ⟩

/-- The full genuine derivative quotient is continuously complex-linearly
isomorphic to the continuous dual of the full native Petersson Hilbert space. -/
def dualityEquiv : TangentQuotient Γ ≃L[ℂ] StrongDual ℂ Q :=
  ContinuousLinearEquiv.ofBijective (quotientPairing R P p hp F hF)
    (quotientPairing_ker R P p hp F hF)
    (LinearMap.range_eq_top.mpr (quotientPairing_surjective R P p hp F hF))

/-- The isomorphism is induced by the literal book integral on representatives. -/
theorem dualityEquiv_apply_mk (μ : B) (q : Q) :
    dualityEquiv R P p hp F hF (Submodule.Quotient.mk μ) q =
      ∫ z in UpperHalfPlane.coe '' F,
        GammaMeasurableBeltrami.planeRepresentative μ.val z *
          QuadraticBergman.uniformizedQuadratic R p
            (toQuadratic R P p hp F hF q) z :=
  pairing_eq_planar R P p hp F hF μ q

end LowDimensionalTopology.Geometry.Teichmuller.NativePetersson
