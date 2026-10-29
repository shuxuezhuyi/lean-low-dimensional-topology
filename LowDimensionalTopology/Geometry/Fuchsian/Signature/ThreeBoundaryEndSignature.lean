/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.Existence
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- A genuine genus-zero Fuchsian signature with no elliptic or cusp
classes and exactly three boundary-hyperbolic end classes is realized. -/
theorem exists_three_boundary_end_signature :
    ∃ H : Subgroup Mobius.complexMobiusGroup, ∃ P : UnitDiscFuchsianGroup H,
      ∃ hNE : DiscreteGroups.IsNonElementary H, ∃ hFG : H.FG,
        HasNielsenFuchsianSignature P hNE hFG 0 [] 0 3 := by
  apply generalSignature_realization_exists 0 [] 0 3
  · simp
  · norm_num [generalCoreDeficit]

/-- This genuine signature has Nielsen-core area equal to twice pi. -/
theorem three_boundary_end_nielsen_area
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {hNE : DiscreteGroups.IsNonElementary H}
    {hFG : H.FG}
    (h : HasNielsenFuchsianSignature P hNE hFG 0 [] 0 3)
    {D : Set P.domain.carrier} (hD : IsFuchsianFundamentalDomain P D) :
    (fuchsianNielsenCoreArea P hNE D).toReal = 2 * Real.pi := by
  have ha := h.area hD
  norm_num at ha
  exact ha

/-- A realized three-boundary-end signature admits an actual Dirichlet
fundamental domain whose Nielsen-core area is twice pi. -/
theorem exists_three_boundary_end_signature_with_dirichlet_area :
    ∃ H : Subgroup Mobius.complexMobiusGroup, ∃ P : UnitDiscFuchsianGroup H,
      ∃ hNE : DiscreteGroups.IsNonElementary H, ∃ hFG : H.FG,
        HasNielsenFuchsianSignature P hNE hFG 0 [] 0 3 ∧
          ∃ w : P.domain.carrier,
            IsDirichletCenter P w ∧ w ∈ fuchsianNielsenCore P hNE ∧
              IsFuchsianFundamentalDomain P (dirichletDomain P w) ∧
                (fuchsianNielsenCoreArea P hNE (dirichletDomain P w)).toReal =
                  2 * Real.pi := by
  obtain ⟨H, P, hNE, hFG, h⟩ := exists_three_boundary_end_signature
  obtain ⟨w, hw, hwN⟩ := exists_dirichlet_center_in_nielsenCore P hNE
  have hD := dirichletDomain_fundamental P w hw
  exact ⟨H, P, hNE, hFG, h, w, hw, hwN, hD, three_boundary_end_nielsen_area h hD⟩

end LowDimensionalTopology.Geometry.Fuchsian
