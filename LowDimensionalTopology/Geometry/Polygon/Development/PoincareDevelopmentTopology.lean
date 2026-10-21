/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Development.Data
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Homeomorph.Defs
@[expose] public section
noncomputable section
open Set
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.Polygon.PoincarePolygon
variable {X : Type*} [TopologicalSpace X] (P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X)
/-- Polygon-copy points use their actual subspace topology. -/
instance pointTopology : TopologicalSpace P.Point :=
  inferInstanceAs (TopologicalSpace {x : X // x ∈ P.carrier})
end LowDimensionalTopology.Geometry.Polygon.PoincarePolygon

namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
universe u v
open Topology
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)
variable [TopologicalSpace X]

/-- The indexed copies use the original discrete group-index/product topology. -/
instance copyTopology : TopologicalSpace S.Copy := by
  letI : TopologicalSpace S.Generated := ⊥
  exact inferInstanceAs (TopologicalSpace (S.Generated × P.Point))

/-- The development carries the actual quotient topology of the indexed copies. -/
instance developmentTopology : TopologicalSpace S.Development :=
  inferInstanceAs (TopologicalSpace (Quotient S.gluingSetoid))

local instance generatedTopology : TopologicalSpace S.Generated := ⊥
local instance generatedDiscreteTopology : DiscreteTopology S.Generated := ⟨rfl⟩

/-- The genuine original projection is a quotient map for these topologies. -/
theorem isQuotientMap_project : IsQuotientMap S.project := isQuotientMap_quotient_mk'

/-- The actual gluing projection is continuous. -/
theorem continuous_project : Continuous S.project := S.isQuotientMap_project.continuous

/-- Open sets in the development are detected by their actual indexed-copy preimages. -/
theorem isOpen_iff_project_preimage (U : Set S.Development) :
    IsOpen U ↔ IsOpen (S.project ⁻¹' U) := S.isQuotientMap_project.isOpen_preimage

/-- Original evaluation on the copies is continuous, with no ambient discreteness assumption. -/
theorem continuous_copyEvaluation [ContinuousConstSMul Γ X] : Continuous S.copyEvaluation := by
  change Continuous (fun a : S.Generated × P.Point => a.1 • a.2.val)
  apply continuous_prod_of_discrete_left.mpr
  intro g
  exact (continuous_const_smul (g.val : Γ)).comp continuous_subtype_val

/-- Evaluation on the actual glued quotient is continuous. -/
theorem continuous_evaluation [ContinuousConstSMul Γ X] : Continuous S.evaluation :=
  S.continuous_copyEvaluation.quotient_lift (fun _ _ h => S.gluing_evaluation h)

/-- Changing a discrete group index is a genuine continuous map of the original copies. -/
theorem continuous_translateCopy (g : S.Generated) : Continuous (S.translateCopy g) := by
  change Continuous (fun a : S.Generated × P.Point => (g*a.1,a.2))
  exact ((continuous_of_discreteTopology (f := fun h : S.Generated => g*h)).comp
    continuous_fst).prodMk continuous_snd

/-- Every actual generated element acts continuously on the glued quotient. -/
theorem continuous_translate (g : S.Generated) : Continuous (S.translate g) :=
  continuous_quot_map (fun _ _ h => S.gluing_translate g h) (S.continuous_translateCopy g)

/-- The actual left-translation action on the development consists of homeomorphisms. -/
def translationHomeomorph (g : S.Generated) : S.Development ≃ₜ S.Development where
  toEquiv := MulAction.toPermHom S.Generated S.Development g
  continuous_toFun := S.continuous_translate g
  continuous_invFun := S.continuous_translate g⁻¹

@[simp] theorem translationHomeomorph_apply (g : S.Generated) (q : S.Development) :
    S.translationHomeomorph g q = g • q := rfl

/-- A finite or infinite generated word evaluates equivariantly under the actual quotient homeomorphism. -/
theorem evaluation_translationHomeomorph (g : S.Generated) (q : S.Development) :
    S.evaluation (S.translationHomeomorph g q) = g • S.evaluation q := S.evaluation_smul g q

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
