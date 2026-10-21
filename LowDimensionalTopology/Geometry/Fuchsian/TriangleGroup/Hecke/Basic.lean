/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleReflectionGroups
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Surfaces

/-- The infinite second order is included. -/
def IsHeckeGroup (G : Subgroup (ℍ ≃ᵢ ℍ)) : Prop :=
  ∃ q : ℕ∞, 3≤q ∧ IsTriangleGroupOfOrders G 2 q ⊤

theorem isHeckeGroup_iff (G : Subgroup (ℍ ≃ᵢ ℍ)) :
    IsHeckeGroup G ↔ ∃q : ℕ∞, 3≤q ∧
      IsConformalTriangleType G (Real.pi/2) (triangleOrderAngle q) 0 := by
  have htwo : triangleOrderAngle 2=Real.pi/2 := by norm_num [triangleOrderAngle]
  constructor
  · rintro ⟨q,hq,hG⟩
    refine ⟨q,hq,?_⟩
    simpa only [htwo,triangleOrderAngle_top] using hG.2.2.2
  · rintro ⟨q,hq,hG⟩
    refine ⟨q,hq,by norm_num,le_trans (by norm_num : (2:ℕ∞)≤3) hq,by simp,?_⟩
    simpa only [htwo,triangleOrderAngle_top] using hG

theorem IsHeckeGroup.isTriangleGroup {G : Subgroup (ℍ ≃ᵢ ℍ)} (hG : IsHeckeGroup G) :
    IsTriangleGroup G := by
  obtain ⟨q,_,hq⟩:=hG
  exact ⟨2,q,⊤,hq⟩

theorem isHeckeGroup_of_orders {G : Subgroup (ℍ ≃ᵢ ℍ)} (q : ℕ∞) (hq : 3≤q)
    (hG : IsTriangleGroupOfOrders G 2 q ⊤) : IsHeckeGroup G := ⟨q,hq,hG⟩

theorem isHeckeGroup_of_finite_orders {G : Subgroup (ℍ ≃ᵢ ℍ)} (q : ℕ) (hq : 3≤q)
    (hG : IsTriangleGroupOfOrders G 2 q ⊤) : IsHeckeGroup G := by
  apply isHeckeGroup_of_orders q _ hG
  exact_mod_cast hq

theorem isHeckeGroup_of_infinite_order {G : Subgroup (ℍ ≃ᵢ ℍ)}
    (hG : IsTriangleGroupOfOrders G 2 ⊤ ⊤) : IsHeckeGroup G :=
  ⟨⊤,le_top,hG⟩

end LowDimensionalTopology.Geometry.Fuchsian
