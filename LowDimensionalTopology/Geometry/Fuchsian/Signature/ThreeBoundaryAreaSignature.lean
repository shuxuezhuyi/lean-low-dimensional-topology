module

public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.QuotientSignature
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.FinitelyGeneratedCyclicClasses
public import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- Three genuine boundary classes and the actual core-area bound force the pants signature. -/
theorem three_boundary_area_forces_signature
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (hFG : H.FG)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬ Mobius.MobiusElliptic f)
    (hboundary : 3 ≤ Nat.card
      (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc))
    (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (harea : fuchsianNielsenCoreArea P hNE (dirichletDomain P w) ≤
      ENNReal.ofReal (2 * Real.pi)) :
    HasNielsenFuchsianSignature P hNE hFG 0 [] 0 3 := by
  let : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic) :=
    finitelyGenerated_unitDisc_cyclic_classes_finite P hNE hFG .elliptic
  have hnil : fuchsianEllipticOrderList P.asFuchsianDisc = [] :=
    (fuchsianEllipticOrderList_eq_nil_iff P.asFuchsianDisc).mpr
      (fun f hf he => hno f hf he.1 he)
  obtain ⟨g, orders, c, t, hSig⟩ := finitelyGenerated_hasNielsenFuchsianSignature P hNE hFG
  have hSaved := hSig
  obtain ⟨_w, _hw, _hwN, _J, _hc, _hv, _n, _S, _hr, _hg, hPerm, _hcusp, hbound⟩ := hSig
  have hOrdersNil : orders = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [hPerm.length_eq, hnil]
    rfl
  subst orders
  have ht3 : 3 ≤ t := by simpa only [hbound] using hboundary
  have hBudget := hSaved.area (dirichletDomain_fundamental P w hw)
  simp only [List.map_nil, List.sum_nil, add_zero] at hBudget
  have hReal : (fuchsianNielsenCoreArea P hNE (dirichletDomain P w)).toReal ≤
      2 * Real.pi := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top harea
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)] using hh
  have hDelta : 2 * (g : ℝ) - 2 + (t : ℝ) + (c : ℝ) ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_left (by positivity : 0 < 2 * Real.pi)).mp
    nlinarith only [hBudget, hReal]
  have hNat : 2 * g + t + c ≤ 3 := by
    exact_mod_cast (show 2 * (g : ℝ) + (t : ℝ) + (c : ℝ) ≤ 3 by
      linarith only [hDelta])
  obtain ⟨rfl, rfl, rfl⟩ : g = 0 ∧ c = 0 ∧ t = 3 := by omega
  exact hSaved

end LowDimensionalTopology.Geometry.Fuchsian
