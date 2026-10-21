module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.TorusFundamentalGroup
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
@[expose] public section
noncomputable section
namespace LowDimensionalTopology.Geometry.Surfaces

/-- Integral rank prevents a smaller free abelian group from mapping onto a larger one. -/
theorem intPiHom_not_surjective_of_lt {m n : ℕ} (hmn : m < n)
    (f : (Fin m → ℤ) →+ (Fin n → ℤ)) : ¬Function.Surjective f := by
  intro hf
  have h := LinearMap.finrank_le_finrank_of_surjective (f := f.toIntLinearMap) hf
  simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
  omega


/-- The actual fundamental group of a two-torus cannot map onto three independent winding numbers. -/
theorem torusProductFundamentalGroup_not_surjective_three_windings
    (x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ))
    (f : FundamentalGroup (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) x →*
      (Fin 3 → Multiplicative ℤ)) : ¬Function.Surjective f := by
  intro hf
  let e : Multiplicative (Fin 2 → ℤ) ≃*
      FundamentalGroup (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) x :=
    ((MulEquiv.piMultiplicative (fun _ : Fin 2 => ℤ)).trans
      (piFinTwoMulEquiv (Multiplicative ℤ))).trans
      (torusProductFundamentalGroupEquiv x).symm
  let h : Multiplicative (Fin 2 → ℤ) →* Multiplicative (Fin 3 → ℤ) :=
    (MulEquiv.piMultiplicative (fun _ : Fin 3 => ℤ)).symm.toMonoidHom.comp
      (f.comp e.toMonoidHom)
  have hh : Function.Surjective h :=
    (MulEquiv.piMultiplicative (fun _ : Fin 3 => ℤ)).symm.surjective.comp
      (hf.comp e.surjective)
  let k : (Fin 2 → ℤ) →+ (Fin 3 → ℤ) := h.toAdditiveLeft
  exact intPiHom_not_surjective_of_lt (by decide : 2 < 3) k hh

/-- A simply connected space has no surjective triple of integral winding numbers. -/
theorem fundamentalGroup_not_surjective_three_windings_of_simplyConnected
    {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (f : FundamentalGroup X x →* (Fin 3 → Multiplicative ℤ)) :
    ¬Function.Surjective f := by
  intro hf
  obtain ⟨p, hp⟩ := hf (fun _ => Multiplicative.ofAdd (1 : ℤ))
  have he : p = 1 := Subsingleton.elim _ _
  rw [he, map_one] at hp
  have hz : (0 : ℤ) = 1 := congrArg (fun v : Fin 3 → Multiplicative ℤ => (v 0).toAdd) hp
  exact zero_ne_one hz

/-- Three independent actual winding numbers rule out a homeomorphism to the actual two-torus. -/
theorem not_homeomorphic_torus_of_surjective_three_windings
    {X : Type*} [TopologicalSpace X] (x : X)
    (f : FundamentalGroup X x →* (Fin 3 → Multiplicative ℤ))
    (hf : Function.Surjective f) :
    ¬Nonempty (X ≃ₜ AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) := by
  rintro ⟨e⟩
  let E := fundamentalGroupHomeomorphMulEquiv e x
  exact torusProductFundamentalGroup_not_surjective_three_windings (e x)
    (f.comp E.symm.toMonoidHom) (hf.comp E.symm.surjective)

end LowDimensionalTopology.Geometry.Surfaces
