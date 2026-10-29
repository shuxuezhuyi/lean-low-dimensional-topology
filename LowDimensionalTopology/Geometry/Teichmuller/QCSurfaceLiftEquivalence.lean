module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCMarkedSpace
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S27_TeichmullerExistence

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

universe u v
variable (R : Surface.{u}) (S : Surface.{v})
    {Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} {q : ℍ → S.carrier}
    (hp : LiZhongQC.IsUniformization Γ p) (hq : LiZhongQC.IsUniformization Δ q)
    (f : R.carrier ≃ₜ S.carrier)

include hp hq

/-- The original chart definition and every genuine covering lift have exactly
the same quasiconformal distortion constant. -/
theorem isKQCRS_iff_given_lift {F : ℍ ≃ₜ ℍ}
    (hF : LiZhongQC.IsLift p q f F) (K : ℝ) :
    LiZhongQC.IsKQCRS f K ↔
      LiZhongQC.IsKQC (LiZhongQC.liftToC F) LiZhongQC.upperHalf K := by
  constructor
  · intro hf
    exact LiZhongQC.h23l_lift_isKQC hp hq hf hF
  · intro hK
    exact LiZhongQC.s27v_isKQCRS_of_lift hp hq hF hK

/-- Quasiconformality of the original surface map is equivalent to that of
any specified lift, with no closedness or finite-type requirement. -/
theorem isQCRS_iff_given_lift {F : ℍ ≃ₜ ℍ}
    (hF : LiZhongQC.IsLift p q f F) :
    LiZhongQC.IsQCRS f ↔
      ∃ K : ℝ, LiZhongQC.IsKQC (LiZhongQC.liftToC F) LiZhongQC.upperHalf K := by
  change (∃ K : ℝ, LiZhongQC.IsKQCRS f K) ↔ _
  exact exists_congr (fun K => isKQCRS_iff_given_lift R S hp hq f hF K)

/-- Choosing a different actual lift does not alter any distortion bound. -/
theorem given_lifts_isKQC_iff {F G : ℍ ≃ₜ ℍ}
    (hF : LiZhongQC.IsLift p q f F) (hG : LiZhongQC.IsLift p q f G) (K : ℝ) :
    LiZhongQC.IsKQC (LiZhongQC.liftToC F) LiZhongQC.upperHalf K ↔
      LiZhongQC.IsKQC (LiZhongQC.liftToC G) LiZhongQC.upperHalf K :=
  (isKQCRS_iff_given_lift R S hp hq f hF K).symm.trans
    (isKQCRS_iff_given_lift R S hp hq f hG K)

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
