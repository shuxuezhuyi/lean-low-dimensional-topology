module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.TorusFundamentalGroup
public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Complex.CoveringMap

/-!
# Fundamental groups of ordinary circular planar domains

Mathlib's actual radial homeomorphism identifies each circular band with
`Circle` times its genuine open radius interval. The interval factor is
contractible. These topological computations will be used for the converse
in the classification of original Riemann surfaces with abelian fundamental
group; no complex structure is transported or replaced here.
-/

public section
noncomputable section

open Set Metric

namespace LowDimensionalTopology.Geometry.Surfaces

/-- The actual radial-coordinate homeomorphism on an ordinary circular band. -/
def circularBandHomeomorph (a b : ℝ) (ha : 0 ≤ a) :
    {z : ℂ // a < ‖z‖ ∧ ‖z‖ < b} ≃ₜ Circle × Ioo a b := by
  let E := homeomorphUnitSphereProd ℂ
  let e₀ : {z : ℂ // a < ‖z‖ ∧ ‖z‖ < b} ≃ₜ
      {z : ({0}ᶜ : Set ℂ) // a < ‖z.val‖ ∧ ‖z.val‖ < b} :=
    { toFun := fun z => ⟨⟨z.val, by
        change z.val ≠ 0
        exact norm_pos_iff.mp (ha.trans_lt z.property.1)⟩, z.property⟩
      invFun := fun z => ⟨z.val.val, z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let e₁ := E.subtype
    (p := fun z => a < ‖z.val‖ ∧ ‖z.val‖ < b)
    (q := fun z : Circle × Ioi (0 : ℝ) => a < z.2.val ∧ z.2.val < b)
    (fun z => by
      dsimp only [E, homeomorphUnitSphereProd, homeomorphSphereProd]
      simp only [div_one]
      rfl)
  let e₂ : {z : Circle × Ioi (0 : ℝ) // a < z.2.val ∧ z.2.val < b} ≃ₜ
      Circle × Ioo a b :=
    { toFun := fun z => (z.val.1, ⟨z.val.2.val, z.property⟩)
      invFun := fun z => ⟨(z.1, ⟨z.2.val, ha.trans_lt z.2.property.1⟩), z.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact (e₀.trans e₁).trans e₂

/-- The actual based fundamental group of the ordinary circle is commutative. -/
theorem circleFundamentalGroup_commute (x : Circle)
    (p q : FundamentalGroup Circle x) : Commute p q := by
  change p * q = q * p
  apply (Circle.fundamentalGroupMulEquiv x).injective
  rw [map_mul, map_mul, mul_comm]

/-- Every ordinary nonempty circular band has abelian based fundamental group.
Its entire radius interval, rather than a chosen circle, remains in the type. -/
theorem circularBandFundamentalGroup_commute (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (x : {z : ℂ // a < ‖z‖ ∧ ‖z‖ < b})
    (p q : FundamentalGroup {z : ℂ // a < ‖z‖ ∧ ‖z‖ < b} x) : Commute p q := by
  let : ContractibleSpace (Ioo a b) :=
    (convex_Ioo a b).contractibleSpace (nonempty_Ioo.mpr hab)
  let E := circularBandHomeomorph a b ha
  let j := (fundamentalGroupHomeomorphMulEquiv E x).trans
    (fundamentalGroupProdMulEquiv (E x).1 (E x).2)
  change p * q = q * p
  apply j.injective
  rw [map_mul, map_mul]
  apply Prod.ext
  · exact (circleFundamentalGroup_commute (E x).1 (j p).1 (j q).1).eq
  · exact Subsingleton.elim _ _

/-- The actual exponential quotient-cover computes commutativity on the
ordinary punctured plane at every basepoint. -/
theorem puncturedPlaneFundamentalGroup_commute (x : {z : ℂ // z ≠ 0})
    (p q : FundamentalGroup {z : ℂ // z ≠ 0} x) : Commute p q := by
  let hp := Complex.isAddQuotientCoveringMap_exp
  obtain ⟨z, hz⟩ := hp.surjective x
  let j := hp.fundamentalGroupEquiv (x := x) ⟨z, hz⟩
  change p * q = q * p
  apply j.injective
  rw [map_mul, map_mul]
  exact mul_comm (j p) (j q)

end LowDimensionalTopology.Geometry.Surfaces
