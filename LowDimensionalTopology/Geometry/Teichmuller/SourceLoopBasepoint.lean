module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Closed
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Covering
public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
public import LowDimensionalTopology.External.TauCeti.Topology.Homotopy.HomotopyGroup.Collar

/-! Move the basepoint of an original loop using the existing one-dimensional
collar homotopy. The source path and resulting based loop precede every target. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped unitInterval

namespace LowDimensionalTopology.Geometry.Surfaces

/-- Transport along an actual source path gives a loop at its far endpoint in
the same original free class; both homotopy endpoints trace that same path. -/
theorem freelyHomotopic_loop_at_of_path
    {X : Type} [TopologicalSpace X] (α : LiZhongQC.Loop X) {b : X} (η : Path α.1 b) :
    ∃ β : Path b b, LiZhongQC.FreelyHomotopic α ⟨b, β⟩ := by
  let f := (genLoopEquivOfUnique (Fin 1) (X := X) (x := α.1)).symm α.2
  let β : Path b b := genLoopEquivOfUnique (Fin 1) (TauCeti.GenLoop.transport η f)
  let H := TauCeti.GenLoop.collarHomotopyAlong η f
  have hf (t : I) : f (fun _ => t) = α.2 t :=
    congrArg (fun p : Path α.1 α.1 => p t)
      ((genLoopEquivOfUnique (Fin 1) (X := X) (x := α.1)).apply_symm_apply α.2)
  refine ⟨β, ⟨⟨fun st => H (st.1, fun _ => st.2),
    H.toHomotopy.continuous.comp
      (continuous_fst.prodMk (continuous_pi (fun _ => continuous_snd)))⟩, ?_, ?_, ?_⟩⟩
  · intro t
    exact (H.map_zero_left (fun _ => t)).trans (hf t)
  · intro t
    exact H.map_one_left (fun _ => t)
  · intro s
    exact (H.map_boundary s (fun _ : Fin 1 => (0 : I)) ⟨0, Or.inl rfl⟩).trans
      (H.map_boundary s (fun _ : Fin 1 => (1 : I)) ⟨0, Or.inr rfl⟩).symm

/-- The original closed Riemann surface supplies the source path, hence every
original free class has a representative at any prescribed original vertex. -/
theorem ClosedRiemannSurface.exists_source_based_loop
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (α : LiZhongQC.Loop X) (b : X) :
    ∃ β : Path b b, LiZhongQC.FreelyHomotopic α ⟨b, β⟩ := by
  let := R.toRiemannSurface.pathConnectedSpace
  exact freelyHomotopic_loop_at_of_path α (PathConnectedSpace.somePath α.1 b)

end LowDimensionalTopology.Geometry.Surfaces
