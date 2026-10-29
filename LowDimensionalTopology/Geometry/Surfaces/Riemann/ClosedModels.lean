module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureCofiniteExistenceConsumer
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Closed complex surfaces of every genus

Cofinite Fuchsian realization with five auxiliary elliptic classes gives an
actual compact complex surface of any prescribed topological genus. The cone
metric of that auxiliary orbifold is not used as a smooth hyperbolic metric.
For genus at least two, uniformization supplies a new, nonelliptic hyperbolic
quotient model on the resulting closed Riemann surface.
-/

@[expose] public section

noncomputable section

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Mobius

theorem genusSurfacePresentation_exists (g : ℕ) :
    ∃ H : Subgroup complexMobiusGroup, ∃ P : UnitDiscFuchsianGroup H,
      HasCofiniteFuchsianSignature P.asFuchsianDisc g [2, 2, 2, 2, 2] 0 := by
  have horders : ∀ m ∈ ([2, 2, 2, 2, 2] : List ℕ), 2 ≤ m := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hm
    exact hm.ge
  have hdef : 0 < 2 * (g : ℝ) - 2 + ((0 : ℕ) : ℝ) +
      (([2, 2, 2, 2, 2] : List ℕ).map (fun m : ℕ => 1 - 1 / (m : ℝ))).sum := by
    have hg : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg g
    norm_num; linarith
  obtain ⟨H, P, _hFG, _hfirst, _hNielsen, hSig, _hpolygon⟩ :=
    generalSignature_cofinite_realization_exists g [2, 2, 2, 2, 2] 0 horders hdef
  exact ⟨H, P, hSig⟩

def genusSurfaceGroup (g : ℕ) : Subgroup complexMobiusGroup :=
  (genusSurfacePresentation_exists g).choose

theorem genusSurfaceDiscData (g : ℕ) : UnitDiscFuchsianGroup (genusSurfaceGroup g) :=
  (genusSurfacePresentation_exists g).choose_spec.choose

theorem genusSurfaceSignature (g : ℕ) :
    HasCofiniteFuchsianSignature (genusSurfaceDiscData g).asFuchsianDisc g [2, 2, 2, 2, 2] 0 :=
  (genusSurfacePresentation_exists g).choose_spec.choose_spec

/-- An actual compact complex-surface carrier realizing the prescribed genus. -/
def GenusSurfaceCarrier (g : ℕ) : Type :=
  FuchsianCuspCompletion (genusSurfaceDiscData g).asFuchsianDisc

instance genusSurfaceCarrierTopology (g : ℕ) : TopologicalSpace (GenusSurfaceCarrier g) := by
  dsimp only [GenusSurfaceCarrier]
  infer_instance

/-- The genuine complex structure on the completed quotient, with proved compactness. -/
def closedRiemannSurfaceOfGenus (g : ℕ) : ClosedRiemannSurface (GenusSurfaceCarrier g) where
  toRiemannSurface :=
    fuchsianCuspCompletionRiemannSurface (genusSurfaceDiscData g).asFuchsianDisc
  compactSpace := (genusSurfaceSignature g).compact

/-- The genus is the actual handle-model invariant of the constructed surface. -/
theorem closedRiemannSurfaceOfGenus_hasGenus (g : ℕ) :
    (closedRiemannSurfaceOfGenus g).HasGenus g :=
  (genusSurfaceSignature g).topologicalGenus

/-- The constructed surface has an actual homeomorphism to the standard handle model. -/
def genusSurfaceHomeomorph (g : ℕ) : GenusSurfaceCarrier g ≃ₜ CanonicalHandleSurface g :=
  Classical.choice (closedRiemannSurfaceOfGenus_hasGenus g)

/-- Closed Riemann surfaces of every natural genus exist, with a verified genus witness. -/
theorem nonempty_closedRiemannSurfaceOfGenus (g : ℕ) :
    Nonempty { R : ClosedRiemannSurface (GenusSurfaceCarrier g) // R.HasGenus g } :=
  ⟨⟨closedRiemannSurfaceOfGenus g, closedRiemannSurfaceOfGenus_hasGenus g⟩⟩

/-- Uniformization gives a genuine nonelliptic hyperbolic model in every genus at least two. -/
def closedHyperbolicSurfaceOfGenus (g : ℕ) (hg : 2 ≤ g) :
    ClosedHyperbolicSurface (GenusSurfaceCarrier g) :=
  (closedRiemannSurfaceOfGenus g).hyperbolicOfGenusGeTwo hg
    (closedRiemannSurfaceOfGenus_hasGenus g)

@[simp]
theorem closedHyperbolicSurfaceOfGenus_toClosedRiemannSurface (g : ℕ) (hg : 2 ≤ g) :
    (closedHyperbolicSurfaceOfGenus g hg).toClosedRiemannSurface =
      closedRiemannSurfaceOfGenus g := rfl

theorem closedHyperbolicSurfaceOfGenus_hasGenus (g : ℕ) (hg : 2 ≤ g) :
    (closedHyperbolicSurfaceOfGenus g hg).toClosedRiemannSurface.HasGenus g :=
  closedRiemannSurfaceOfGenus_hasGenus g

end LowDimensionalTopology.Geometry.Surfaces
