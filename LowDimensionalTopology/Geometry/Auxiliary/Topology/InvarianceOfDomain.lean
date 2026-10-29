module

public import LowDimensionalTopology.External.LiZhongQC.LiZhongExternal.Topology.InvarianceOfDomain
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The original map as a homeomorphism onto its open domain image

The finite-dimensional invariance-of-domain proof is imported through the
existing unconditional endpoint. Its preserved provenance credits harfe's MIT
Brouwer proof and Kai Lam's Apache-2.0 invariance-of-domain argument.
The conclusion retains the original map and its actual image.
-/

public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Auxiliary.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Every continuous injection of a finite-dimensional real normed space into
itself is an open embedding. -/
theorem finiteDimensional_isOpenEmbedding_of_continuous_injective
    (f : E → E) (hf : Continuous f) (hinj : Function.Injective f) :
    Topology.IsOpenEmbedding f := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hf hinj
  intro U hU
  exact LiZhongExternal.Topology.invariance_of_domain_finiteDimensional
    f U hU hf.continuousOn (fun _ _ _ _ h => hinj h)

/-- The homeomorphism has exactly the given continuous injection as its
underlying map, with the actual range as target. -/
@[expose] def finiteDimensionalHomeomorphRange
    (f : E → E) (hf : Continuous f) (hinj : Function.Injective f) :
    E ≃ₜ Set.range f :=
  (finiteDimensional_isOpenEmbedding_of_continuous_injective f hf hinj).isEmbedding.toHomeomorph

@[simp]
theorem finiteDimensionalHomeomorphRange_apply_coe
    (f : E → E) (hf : Continuous f) (hinj : Function.Injective f) (x : E) :
    (finiteDimensionalHomeomorphRange f hf hinj x : E) = f x := rfl

/-- The actual image is a domain: it is open, nonempty, and connected. -/
theorem finiteDimensional_range_isDomain
    (f : E → E) (hf : Continuous f) (hinj : Function.Injective f) :
    IsOpen (Set.range f) ∧ IsConnected (Set.range f) := by
  refine ⟨(finiteDimensional_isOpenEmbedding_of_continuous_injective f hf hinj).isOpen_range, ?_⟩
  simpa only [Set.image_univ] using
    (isConnected_univ : IsConnected (Set.univ : Set E)).image f hf.continuousOn

/-- Brouwer's domain conclusion and the original-map homeomorphism on real
coordinate space. This includes every dimension at least two. -/
theorem realCoordinate_invariance_of_domain (n : ℕ)
    (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf : Continuous f) (hinj : Function.Injective f) :
    IsOpen (Set.range f) ∧ IsConnected (Set.range f) ∧
      ∃ e : (Fin n → ℝ) ≃ₜ Set.range f, ∀ x, (e x : Fin n → ℝ) = f x := by
  obtain ⟨hopen, hconn⟩ := finiteDimensional_range_isDomain f hf hinj
  refine ⟨hopen, hconn, finiteDimensionalHomeomorphRange f hf hinj, ?_⟩
  intro x
  exact finiteDimensionalHomeomorphRange_apply_coe f hf hinj x

end LowDimensionalTopology.Geometry.Auxiliary.Topology
