module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Covering
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannSphereTopology
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

/-- A nonempty connected covering of a simply connected, locally path connected
space has one sheet. The inverse is obtained by lifting the identity of the base;
uniqueness of lifts makes it a left inverse as well as a right inverse. -/
theorem covering_bijective_of_simplyConnected
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PreconnectedSpace E] [Nonempty E] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] {p : E → X} (hp : IsCoveringMap p) :
    Function.Bijective p := by
  classical
  let e₀ : E := Classical.choice inferInstance
  obtain ⟨g, ⟨hg₀, hpg⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts (ContinuousMap.id X) (p e₀) e₀ rfl
  have hgp : (g ∘ p : E → E) = id :=
    hp.eq_of_comp_eq (g.continuous.comp hp.continuous) continuous_id
      (by
        funext e
        exact congrFun hpg (p e)) e₀ hg₀
  have hleft : Function.LeftInverse g p := fun e => congrFun hgp e
  exact ⟨hleft.injective, fun x => ⟨g x, congrFun hpg x⟩⟩

/-- Every local homeomorphism of the genuine Riemann sphere onto itself is
bijective. Compactness upgrades the local homeomorphism to a covering; simple
connectedness rules out multiple sheets. -/
theorem riemannSphere_localHomeomorph_bijective
    (f : OnePoint ℂ → OnePoint ℂ) (hf : IsLocalHomeomorph f) :
    Function.Bijective f := by
  let : SimplyConnectedSpace (OnePoint ℂ) := riemannSphere_simplyConnected
  let : LocallyPathConnectedSpace (OnePoint ℂ) :=
    sphereRiemannAtlas.locallyPathConnectedSpace
  exact covering_bijective_of_simplyConnected
    (isLocalHomeomorph_iff_isCoveringMap.mp hf)

/-- The global sphere homeomorphism determined by a local homeomorphism. -/
def riemannSphereLocalHomeomorph
    (f : OnePoint ℂ → OnePoint ℂ) (hf : IsLocalHomeomorph f) :
    OnePoint ℂ ≃ₜ OnePoint ℂ :=
  hf.toHomeomorphOfBijective (riemannSphere_localHomeomorph_bijective f hf)

@[simp]
theorem riemannSphereLocalHomeomorph_apply
    (f : OnePoint ℂ → OnePoint ℂ) (hf : IsLocalHomeomorph f) (z : OnePoint ℂ) :
    riemannSphereLocalHomeomorph f hf z = f z := rfl

/-- A local homeomorphism of the Riemann sphere is the underlying map of a
global homeomorphism; neither injectivity nor surjectivity is assumed. -/
theorem riemannSphere_localHomeomorph_exists_homeomorph
    (f : OnePoint ℂ → OnePoint ℂ) (hf : IsLocalHomeomorph f) :
    ∃ e : OnePoint ℂ ≃ₜ OnePoint ℂ, (e : OnePoint ℂ → OnePoint ℂ) = f :=
  ⟨riemannSphereLocalHomeomorph f hf, rfl⟩

end LowDimensionalTopology.Geometry.Surfaces
