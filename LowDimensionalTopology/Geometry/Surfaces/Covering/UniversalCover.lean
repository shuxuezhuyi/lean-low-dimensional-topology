module
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Homotopy.Lifting
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Covering
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Homotopy.LocallyContractible
@[expose] public section
noncomputable section
open Set Topology CategoryTheory
namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type*} [TopologicalSpace X]

/-- The fiber consists of actual endpoint-preserving path homotopy classes. -/
abbrev BasedPathFiber (x₀ x : X) := FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x

/-- The set underlying the based-path construction of the universal covering space. -/
abbrev BasedPathTotalSpace (x₀ : X) :=
  Bundle.TotalSpace (BasedPathFiber x₀ x₀) (BasedPathFiber x₀)

def basedPathEndpoint (x₀ : X) : BasedPathTotalSpace x₀ → X := Bundle.TotalSpace.proj

theorem basedPathEndpoint_surjective [PathConnectedSpace X] (x₀ : X) :
    Function.Surjective (basedPathEndpoint x₀) := by
  intro x
  exact ⟨⟨x, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x)⟩, rfl⟩

/-- A path inside the chosen small neighborhood is mapped into the ambient path groupoid. -/
def localPathClass (U : Set X) [PathConnectedSpace U] (x y : U) :
    FundamentalGroupoid.mk x.val ⟶ FundamentalGroupoid.mk y.val :=
  (FundamentalGroupoid.map (ContinuousMap.subtypeVal U)).map
    (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y))

theorem localPathClass_eq_map (U : Set X) [SimplyConnectedSpace U] (x y : U) (p : Path x y) :
    localPathClass U x y = Path.Homotopic.Quotient.mk (p.map continuous_subtype_val) := by
  change (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y)).map
      (ContinuousMap.subtypeVal U) =
    (Path.Homotopic.Quotient.mk p).map (ContinuousMap.subtypeVal U)
  exact congrArg (fun γ : Path.Homotopic.Quotient x y => γ.map (ContinuousMap.subtypeVal U))
    (Subsingleton.elim _ _)

theorem localPathClass_comp (U : Set X) [SimplyConnectedSpace U] (x y z : U) :
    localPathClass U x y ≫ localPathClass U y z = localPathClass U x z := by
  change (FundamentalGroupoid.map (ContinuousMap.subtypeVal U)).map _ ≫
    (FundamentalGroupoid.map (ContinuousMap.subtypeVal U)).map _ =
      (FundamentalGroupoid.map (ContinuousMap.subtypeVal U)).map _
  rw [← Functor.map_comp]
  exact congrArg (fun γ : Path.Homotopic.Quotient x z =>
    (FundamentalGroupoid.map (ContinuousMap.subtypeVal U)).map γ)
    (Subsingleton.elim _ _)

theorem localPathClass_refl (U : Set X) [SimplyConnectedSpace U] (x : U) :
    localPathClass U x x = 𝟙 (FundamentalGroupoid.mk x.val) := by
  rw [localPathClass_eq_map U x x (Path.refl x)]
  rfl

/-- Concatenation with a fixed actual path class identifies each local fiber with a fixed fiber. -/
def basedPathLocalFiberEquiv (x₀ : X) (U : Set X) [PathConnectedSpace U] (u : U) (x : U) :
    BasedPathFiber x₀ x.val ≃ BasedPathFiber x₀ u.val where
  toFun p := p ≫ Groupoid.inv (localPathClass U u x)
  invFun p := p ≫ localPathClass U u x
  left_inv p := by simp [Category.assoc]
  right_inv p := by simp [Category.assoc]

/-- A reference path to every point, using paths wholly inside the local neighborhood when possible. -/
def basedPathLocalReference [PathConnectedSpace X] (x₀ : X) (U : Set X) [PathConnectedSpace U]
    (u : U) (p : BasedPathFiber x₀ u.val) (x : X) : BasedPathFiber x₀ x :=
  by
    classical
    exact if hx : x ∈ U then p ≫ localPathClass U u ⟨x, hx⟩
    else Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x)

theorem basedPathLocalReference_of_mem [PathConnectedSpace X] (x₀ : X) (U : Set X)
    [PathConnectedSpace U] (u : U) (p : BasedPathFiber x₀ u.val) (x : X) (hx : x ∈ U) :
    basedPathLocalReference x₀ U u p x = p ≫ localPathClass U u ⟨x, hx⟩ := by
  simp only [basedPathLocalReference, dite_eq_left hx]

/-- The actual set-level local trivialization of the based path total space. No topology or
covering theorem is asserted here before continuity of the transition maps is proved. -/
def basedPathPretrivialization [PathConnectedSpace X] (x₀ : X) (U : Set X) (hU : IsOpen U)
    [PathConnectedSpace U] (u : U) (p : BasedPathFiber x₀ u.val)
    [TopologicalSpace (BasedPathFiber x₀ x₀)] :
    Bundle.Pretrivialization (BasedPathFiber x₀ x₀) (basedPathEndpoint x₀) where
  toFun z := (z.proj, z.snd ≫ Groupoid.inv (basedPathLocalReference x₀ U u p z.proj))
  invFun z := ⟨z.1, z.2 ≫ basedPathLocalReference x₀ U u p z.1⟩
  source := basedPathEndpoint x₀ ⁻¹' U
  target := U ×ˢ Set.univ
  map_source' _ hz := ⟨hz, Set.mem_univ _⟩
  map_target' _ hz := hz.1
  left_inv' := by
    rintro ⟨x, γ⟩ _hx
    congr 1
    simp [Category.assoc]
  right_inv' := by
    rintro ⟨x, γ⟩ _hx
    change (x, (γ ≫ basedPathLocalReference x₀ U u p x) ≫
      Groupoid.inv (basedPathLocalReference x₀ U u p x)) = (x, γ)
    simp [Category.assoc]
  open_target := hU.prod isOpen_univ
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- Within a simply connected neighborhood, continuation agrees with every actual internal path. -/
theorem basedPathLocalReference_transport [PathConnectedSpace X] (x₀ : X) (U : Set X)
    [SimplyConnectedSpace U] (u : U) (p : BasedPathFiber x₀ u.val) (x y : U) (r : Path x y) :
    basedPathLocalReference x₀ U u p y.val =
      basedPathLocalReference x₀ U u p x.val ≫
        Path.Homotopic.Quotient.mk (r.map continuous_subtype_val) := by
  rw [basedPathLocalReference_of_mem _ _ _ _ _ y.property,
    basedPathLocalReference_of_mem _ _ _ _ _ x.property,
    Category.assoc, ← localPathClass_eq_map U x y r, localPathClass_comp]

/-- The relative based loop used by transition coordinates. -/
def basedPathLocalTransition [PathConnectedSpace X] (x₀ : X) (U V : Set X)
    [PathConnectedSpace U] [PathConnectedSpace V] (u : U) (v : V)
    (p : BasedPathFiber x₀ u.val) (q : BasedPathFiber x₀ v.val) (x : X) : BasedPathFiber x₀ x₀ :=
  basedPathLocalReference x₀ U u p x ≫ Groupoid.inv (basedPathLocalReference x₀ V v q x)

/-- On every path-connected piece of an overlap of simply connected neighborhoods,
the true path-class transition is constant. -/
theorem basedPathLocalTransition_eq_on_pathConnected [PathConnectedSpace X] (x₀ : X)
    (U V : Set X) [SimplyConnectedSpace U] [SimplyConnectedSpace V] (u : U) (v : V)
    (p : BasedPathFiber x₀ u.val) (q : BasedPathFiber x₀ v.val)
    (W : Set X) [PathConnectedSpace W] (hWU : W ⊆ U) (hWV : W ⊆ V) (x y : W) :
    basedPathLocalTransition x₀ U V u v p q x.val =
      basedPathLocalTransition x₀ U V u v p q y.val := by
  let r := PathConnectedSpace.somePath x y
  let rU : Path (⟨x.val, hWU x.property⟩ : U) ⟨y.val, hWU y.property⟩ := r.map (continuous_inclusion hWU)
  let rV : Path (⟨x.val, hWV x.property⟩ : V) ⟨y.val, hWV y.property⟩ := r.map (continuous_inclusion hWV)
  let rX : Path x.val y.val := r.map continuous_subtype_val
  have hUm : rU.map continuous_subtype_val = rX := by ext t; rfl
  have hVm : rV.map continuous_subtype_val = rX := by ext t; rfl
  have hU := basedPathLocalReference_transport x₀ U u p _ _ rU
  have hV := basedPathLocalReference_transport x₀ V v q _ _ rV
  rw [hUm] at hU
  rw [hVm] at hV
  unfold basedPathLocalTransition
  apply (cancel_mono (basedPathLocalReference x₀ V v q y.val)).mp
  rw [Category.assoc, Category.assoc]
  simp only [Groupoid.inv_comp, Category.comp_id]
  rw [hU, hV]
  simp

theorem basedPathLocalTransition_isLocallyConstant [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    (x₀ : X) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    [SimplyConnectedSpace U] [SimplyConnectedSpace V] (u : U) (v : V)
    (p : BasedPathFiber x₀ u.val) (q : BasedPathFiber x₀ v.val) :
    IsLocallyConstant (fun x : (U ∩ V : Set X) => basedPathLocalTransition x₀ U V u v p q x.val) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨W, ⟨hWo, hxW, hWp⟩, hWsub⟩ :=
    (isOpen_isPathConnected_basis x.val).mem_iff.mp ((hU.inter hV).mem_nhds x.property)
  let : PathConnectedSpace W := isPathConnected_iff_pathConnectedSpace.mp hWp
  filter_upwards [(hWo.preimage continuous_subtype_val).eventually_mem hxW] with y hy
  exact basedPathLocalTransition_eq_on_pathConnected x₀ U V u v p q W
    (fun z hz => (hWsub hz).1) (fun z hz => (hWsub hz).2) ⟨y.val, hy⟩ ⟨x.val, hxW⟩

/-- The true local path-class transition is continuous for the discrete model fiber. -/
theorem basedPathPretrivialization_continuous_transition [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] (x₀ : X) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    [SimplyConnectedSpace U] [SimplyConnectedSpace V] (u : U) (v : V)
    (p : BasedPathFiber x₀ u.val) (q : BasedPathFiber x₀ v.val)
    [TopologicalSpace (BasedPathFiber x₀ x₀)] [DiscreteTopology (BasedPathFiber x₀ x₀)] :
    ContinuousOn
      (basedPathPretrivialization x₀ U hU u p ∘
        (basedPathPretrivialization x₀ V hV v q).toPartialEquiv.symm)
      ((basedPathPretrivialization x₀ V hV v q).target ∩
        (basedPathPretrivialization x₀ V hV v q).toPartialEquiv.symm ⁻¹'
          (basedPathPretrivialization x₀ U hU u p).source) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let S : Set (X × BasedPathFiber x₀ x₀) :=
    (basedPathPretrivialization x₀ V hV v q).target ∩
      (basedPathPretrivialization x₀ V hV v q).toPartialEquiv.symm ⁻¹'
        (basedPathPretrivialization x₀ U hU u p).source
  have hmem (z : S) : z.val.1 ∈ V ∩ U :=
    ⟨z.property.1.1, z.property.2⟩
  have hb : Continuous (fun z : S =>
      (⟨z.val.1, hmem z⟩ : (V ∩ U : Set X))) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hl := (basedPathLocalTransition_isLocallyConstant x₀ V U hV hU v u q p).continuous.comp hb
  have hm : Continuous (fun a : BasedPathFiber x₀ x₀ × BasedPathFiber x₀ x₀ => a.1 ≫ a.2) :=
    continuous_of_discreteTopology
  have ht := (continuous_fst.comp continuous_subtype_val).prodMk
    (hm.comp ((continuous_snd.comp continuous_subtype_val).prodMk hl))
  convert ht using 1
  funext z
  change (z.val.1, (z.val.2 ≫ basedPathLocalReference x₀ V v q z.val.1) ≫
    Groupoid.inv (basedPathLocalReference x₀ U u p z.val.1)) =
      (z.val.1, z.val.2 ≫ basedPathLocalTransition x₀ V U v u q p z.val.1)
  simp only [basedPathLocalTransition, Category.assoc]

def basedPathReferenceFiberEquiv (x₀ x : X) (p : BasedPathFiber x₀ x) :
    BasedPathFiber x₀ x ≃ BasedPathFiber x₀ x₀ where
  toFun γ := γ ≫ Groupoid.inv p
  invFun γ := γ ≫ p
  left_inv γ := by simp [Category.assoc]
  right_inv γ := by simp [Category.assoc]

theorem basedPathPretrivialization_isInducing_fiber [PathConnectedSpace X] (x₀ : X)
    (U : Set X) (hU : IsOpen U) [PathConnectedSpace U] (u : U) (p : BasedPathFiber x₀ u.val)
    [∀ x, TopologicalSpace (BasedPathFiber x₀ x)] [∀ x, DiscreteTopology (BasedPathFiber x₀ x)] (x : X) :
    IsInducing (basedPathPretrivialization x₀ U hU u p ∘
      (Bundle.TotalSpace.mk x : BasedPathFiber x₀ x → BasedPathTotalSpace x₀)) := by
  let E := (basedPathReferenceFiberEquiv x₀ x (basedPathLocalReference x₀ U u p x)).toHomeomorphOfDiscrete
  exact ((isEmbedding_prodMkRight x).comp E.isEmbedding).isInducing

/-- Genuine small simply connected open neighborhoods, with reference paths in the base space. -/
structure BasedPathLocalChart (x₀ : X) where
  carrier : Set X
  isOpen : IsOpen carrier
  simplyConnected : SimplyConnectedSpace carrier
  center : carrier
  reference : BasedPathFiber x₀ center.val

namespace BasedPathLocalChart

def pretrivialization [PathConnectedSpace X] {x₀ : X} (C :
  _root_.LowDimensionalTopology.Geometry.Surfaces.BasedPathLocalChart x₀)
    [TopologicalSpace (_root_.LowDimensionalTopology.Geometry.Surfaces.BasedPathFiber x₀ x₀)] :
    Bundle.Pretrivialization (_root_.LowDimensionalTopology.Geometry.Surfaces.BasedPathFiber x₀ x₀) (_root_.LowDimensionalTopology.Geometry.Surfaces.basedPathEndpoint x₀) := by
  let : SimplyConnectedSpace C.carrier := C.simplyConnected
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.basedPathPretrivialization x₀ C.carrier C.isOpen C.center C.reference

end BasedPathLocalChart

/-- Gluing the actual based-path local trivializations constructs a genuine topology on the total
space. The only continuity input is the proved local constancy of path-class transitions. -/
def basedPathFiberPrebundle [PathConnectedSpace X] [LocallyPathConnectedSpace X] (x₀ : X)
    [∀ x, TopologicalSpace (BasedPathFiber x₀ x)] [∀ x, DiscreteTopology (BasedPathFiber x₀ x)]
    (hlocal : ∀ x : X, ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier) :
    FiberPrebundle (BasedPathFiber x₀ x₀) (BasedPathFiber x₀) where
  pretrivializationAtlas := Set.range (fun C : BasedPathLocalChart x₀ => C.pretrivialization)
  pretrivializationAt x := (hlocal x).choose.pretrivialization
  mem_base_pretrivializationAt x := (hlocal x).choose_spec
  pretrivialization_mem_atlas x := ⟨(hlocal x).choose, rfl⟩
  continuous_trivChange := by
    rintro e ⟨C, rfl⟩ e' ⟨C', rfl⟩
    let : SimplyConnectedSpace C.carrier := C.simplyConnected
    let : SimplyConnectedSpace C'.carrier := C'.simplyConnected
    exact basedPathPretrivialization_continuous_transition x₀ C.carrier C'.carrier
      C.isOpen C'.isOpen C.center C'.center C.reference C'.reference
  totalSpaceMk_isInducing x := by
    let C := (hlocal x).choose
    let : SimplyConnectedSpace C.carrier := C.simplyConnected
    exact basedPathPretrivialization_isInducing_fiber x₀ C.carrier C.isOpen C.center C.reference x

/-- This constructs an actual covering-map topology on the actual based-path homotopy-class
total space. Proving that total space simply connected is a separate remaining obligation. -/
theorem basedPathTotalSpace_exists_coveringTopology [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    (x₀ : X) (hlocal : ∀ x : X, ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier) :
    ∃ T : TopologicalSpace (BasedPathTotalSpace x₀), @IsCoveringMap _ _ T _ (basedPathEndpoint x₀) := by
  let instF : ∀ x, TopologicalSpace (BasedPathFiber x₀ x) := fun _ => ⊥
  let : ∀ x, DiscreteTopology (BasedPathFiber x₀ x) := fun _ => discreteTopology_bot _
  let B := basedPathFiberPrebundle x₀ hlocal
  let T := B.totalSpaceTopology
  let : TopologicalSpace (BasedPathTotalSpace x₀) := T
  let : FiberBundle (BasedPathFiber x₀ x₀) (BasedPathFiber x₀) := B.toFiberBundle
  exact ⟨T, FiberBundle.isCoveringMap⟩

/-- The explicitly constructed covering topology on the actual path-class total space. -/
@[instance_reducible]
def basedPathCoverTopology [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    (x₀ : X) (hlocal : ∀ x : X, ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier) :
    TopologicalSpace (BasedPathTotalSpace x₀) := by
  let instF : ∀ x, TopologicalSpace (BasedPathFiber x₀ x) := fun _ => ⊥
  let : ∀ x, DiscreteTopology (BasedPathFiber x₀ x) := fun _ => discreteTopology_bot _
  exact (basedPathFiberPrebundle x₀ hlocal).totalSpaceTopology

theorem basedPathCover_isCovering [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    (x₀ : X) (hlocal : ∀ x : X, ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier) :
    @IsCoveringMap _ _ (basedPathCoverTopology x₀ hlocal) _ (basedPathEndpoint x₀) := by
  let instF : ∀ x, TopologicalSpace (BasedPathFiber x₀ x) := fun _ => ⊥
  let : ∀ x, DiscreteTopology (BasedPathFiber x₀ x) := fun _ => discreteTopology_bot _
  let B := basedPathFiberPrebundle x₀ hlocal
  let : TopologicalSpace (BasedPathTotalSpace x₀) := B.totalSpaceTopology
  let : FiberBundle (BasedPathFiber x₀ x₀) (BasedPathFiber x₀) := B.toFiberBundle
  change @IsCoveringMap _ _ B.totalSpaceTopology _ (basedPathEndpoint x₀)
  exact FiberBundle.isCoveringMap

variable {Y : Type*} [TopologicalSpace Y]

/-- The actual map into endpoint-preserving path classes obtained from a map of a simply connected
source, with a specified initial path class in the target. -/
@[reducible]
def basedPathMapLift [PathConnectedSpace Y] (x₀ : X) (f : C(Y, X)) (y₀ : Y)
    (p : BasedPathFiber x₀ (f y₀)) (y : Y) : BasedPathTotalSpace x₀ :=
  ⟨f y, p.trans ((Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath y₀ y)).map f)⟩

theorem basedPathMapLift_endpoint [PathConnectedSpace Y] (x₀ : X) (f : C(Y, X)) (y₀ : Y)
    (p : BasedPathFiber x₀ (f y₀)) (y : Y) : basedPathEndpoint x₀ (basedPathMapLift x₀ f y₀ p y) = f y := rfl

theorem basedPathMapLift_at_base [SimplyConnectedSpace Y] (x₀ : X) (f : C(Y, X)) (y₀ : Y)
    (p : BasedPathFiber x₀ (f y₀)) : basedPathMapLift x₀ f y₀ p y₀ = ⟨f y₀, p⟩ := by
  have he : Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath y₀ y₀) =
      Path.Homotopic.Quotient.refl y₀ := Subsingleton.elim _ _
  change Bundle.TotalSpace.mk (f y₀) (p.trans ((Path.Homotopic.Quotient.mk
    (PathConnectedSpace.somePath y₀ y₀)).map f)) = _
  rw [he]
  change Bundle.TotalSpace.mk (f y₀) (p.trans (Path.Homotopic.Quotient.refl (f y₀))) = _
  rw [Path.Homotopic.Quotient.trans_refl]

theorem basedPathMapLift_transport [SimplyConnectedSpace Y] (x₀ : X) (f : C(Y, X)) (y₀ : Y)
    (p : BasedPathFiber x₀ (f y₀)) (y z : Y) (r : Path y z) :
    (basedPathMapLift x₀ f y₀ p z).snd =
      (basedPathMapLift x₀ f y₀ p y).snd ≫ Path.Homotopic.Quotient.mk (r.map f.continuous) := by
  have he : Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath y₀ z) =
      (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath y₀ y)).trans
        (Path.Homotopic.Quotient.mk r) := Subsingleton.elim _ _
  have hmap (a : Path.Homotopic.Quotient y₀ y) (b : Path.Homotopic.Quotient y z) :
      (a.trans b).map f = (a.map f).trans (b.map f) := (FundamentalGroupoid.map f).map_comp a b
  change p.trans ((Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath y₀ z)).map f) =
    (p.trans ((Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath y₀ y)).map f)).trans
      ((Path.Homotopic.Quotient.mk r).map f)
  rw [he, hmap, Path.Homotopic.Quotient.trans_assoc]

def basedPathMapLiftCoordinate [PathConnectedSpace X] [PathConnectedSpace Y] (x₀ : X)
    (f : C(Y, X)) (y₀ : Y) (p : BasedPathFiber x₀ (f y₀))
    (U : Set X) [PathConnectedSpace U] (u : U) (q : BasedPathFiber x₀ u.val) (y : Y) :
    BasedPathFiber x₀ x₀ :=
  (basedPathMapLift x₀ f y₀ p y).snd ≫ Groupoid.inv (basedPathLocalReference x₀ U u q (f y))

theorem basedPathMapLiftCoordinate_eq_on_pathConnected [PathConnectedSpace X] [SimplyConnectedSpace Y]
    (x₀ : X) (f : C(Y, X)) (y₀ : Y) (p : BasedPathFiber x₀ (f y₀))
    (U : Set X) [SimplyConnectedSpace U] (u : U) (q : BasedPathFiber x₀ u.val)
    (W : Set Y) [PathConnectedSpace W] (hWU : ∀ y ∈ W, f y ∈ U) (y z : W) :
    basedPathMapLiftCoordinate x₀ f y₀ p U u q y.val =
      basedPathMapLiftCoordinate x₀ f y₀ p U u q z.val := by
  let r := PathConnectedSpace.somePath y z
  let rY : Path y.val z.val := r.map continuous_subtype_val
  let F : W → U := fun a => ⟨f a.val, hWU a.val a.property⟩
  have hF : Continuous F := (f.continuous.comp continuous_subtype_val).subtype_mk _
  let rU : Path (F y) (F z) := r.map hF
  have hmap : rU.map continuous_subtype_val = rY.map f.continuous := by ext t; rfl
  have hL := basedPathMapLift_transport x₀ f y₀ p y.val z.val rY
  dsimp only [basedPathMapLift] at hL
  have hR := basedPathLocalReference_transport x₀ U u q (F y) (F z) rU
  rw [hmap] at hR
  change basedPathLocalReference x₀ U u q (f z.val) =
    basedPathLocalReference x₀ U u q (f y.val) ≫ Path.Homotopic.Quotient.mk (rY.map f.continuous) at hR
  unfold basedPathMapLiftCoordinate
  apply (cancel_mono (basedPathLocalReference x₀ U u q (f z.val))).mp
  rw [Category.assoc, Category.assoc]
  simp only [Groupoid.inv_comp, Category.comp_id]
  rw [hL, hR]
  simp

theorem basedPathMapLiftCoordinate_isLocallyConstant [PathConnectedSpace X] [SimplyConnectedSpace Y]
    [LocallyPathConnectedSpace Y] (x₀ : X) (f : C(Y, X)) (y₀ : Y) (p : BasedPathFiber x₀ (f y₀))
    (U : Set X) (hU : IsOpen U) [SimplyConnectedSpace U] (u : U) (q : BasedPathFiber x₀ u.val) :
    IsLocallyConstant (fun y : f ⁻¹' U => basedPathMapLiftCoordinate x₀ f y₀ p U u q y.val) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  obtain ⟨W, ⟨hWo, hyW, hWp⟩, hWsub⟩ :=
    (isOpen_isPathConnected_basis y.val).mem_iff.mp ((hU.preimage f.continuous).mem_nhds y.property)
  let : PathConnectedSpace W := isPathConnected_iff_pathConnectedSpace.mp hWp
  filter_upwards [(hWo.preimage continuous_subtype_val).eventually_mem hyW] with z hz
  exact basedPathMapLiftCoordinate_eq_on_pathConnected x₀ f y₀ p U u q W hWsub ⟨z.val, hz⟩ ⟨y.val, hyW⟩

/-- Maps from simply connected, locally path-connected sources lift continuously into the
constructed path-class space, with the displayed path-class formula. -/
theorem basedPathMapLift_continuous [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y] (x₀ : X)
    (hlocal : ∀ x : X, ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier)
    (f : C(Y, X)) (y₀ : Y) (p : BasedPathFiber x₀ (f y₀)) :
    @Continuous _ _ _ (basedPathCoverTopology x₀ hlocal) (basedPathMapLift x₀ f y₀ p) := by
  let instF : ∀ x, TopologicalSpace (BasedPathFiber x₀ x) := fun _ => ⊥
  let : ∀ x, DiscreteTopology (BasedPathFiber x₀ x) := fun _ => discreteTopology_bot _
  let B := basedPathFiberPrebundle x₀ hlocal
  let : TopologicalSpace (BasedPathTotalSpace x₀) := B.totalSpaceTopology
  change @Continuous _ _ _ B.totalSpaceTopology (basedPathMapLift x₀ f y₀ p)
  apply continuous_iff_continuousAt.mpr
  intro y
  let C := (hlocal (f y)).choose
  let : SimplyConnectedSpace C.carrier := C.simplyConnected
  have hyU : f y ∈ C.carrier := (hlocal (f y)).choose_spec
  let e := B.trivializationOfMemPretrivializationAtlas (show C.pretrivialization ∈ B.pretrivializationAtlas
    from ⟨C, rfl⟩)
  have hpre : (basedPathMapLift x₀ f y₀ p) ⁻¹' e.source ∈ nhds y :=
    (C.isOpen.preimage f.continuous).mem_nhds hyU
  apply (e.toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left hpre).mpr
  have hc : ContinuousOn (basedPathMapLiftCoordinate x₀ f y₀ p C.carrier C.center C.reference)
      (f ⁻¹' C.carrier) := continuousOn_iff_continuous_domRestrict.mpr
    (basedPathMapLiftCoordinate_isLocallyConstant x₀ f y₀ p C.carrier C.isOpen C.center C.reference).continuous
  have hca := hc.continuousAt ((C.isOpen.preimage f.continuous).mem_nhds hyU)
  exact f.continuous.continuousAt.prodMk hca

open scoped unitInterval

theorem basedPathTotalSpace_mk_cast (x₀ : X) {x y : X} (h : y = x) (p : BasedPathFiber x₀ x) :
    (⟨y, Path.Homotopic.Quotient.cast p rfl h⟩ : BasedPathTotalSpace x₀) = ⟨x, p⟩ := by
  cases h
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]

theorem pathClass_cast_trans {x y z x' y' z' : X} (hx : x' = x) (hy : y' = y) (hz : z' = z)
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z) :
    (p.cast hx hy).trans (q.cast hy hz) = (p.trans q).cast hx hz := by
  cases hx
  cases hy
  cases hz
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]

theorem unitInterval_simplyConnected : SimplyConnectedSpace I := by
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  infer_instance

theorem unitInterval_locallyPathConnected : LocallyPathConnectedSpace I :=
  (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace

/-- The canonical lift with a prescribed initial path class, built using the simply connected interval. -/
def basedPathLiftCurve [PathConnectedSpace X] [LocallyPathConnectedSpace X] (x₀ : X)
    (hlocal : ∀ x : X, ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier)
    (γ : C(I, X)) (p : BasedPathFiber x₀ (γ 0)) :
    @ContinuousMap I (BasedPathTotalSpace x₀) _ (basedPathCoverTopology x₀ hlocal) := by
  let : SimplyConnectedSpace I := unitInterval_simplyConnected
  let : LocallyPathConnectedSpace I := unitInterval_locallyPathConnected
  let : TopologicalSpace (BasedPathTotalSpace x₀) := basedPathCoverTopology x₀ hlocal
  exact ⟨basedPathMapLift x₀ γ 0 p, basedPathMapLift_continuous x₀ hlocal γ 0 p⟩

theorem basedPathLiftCurve_endpoint [PathConnectedSpace X] [LocallyPathConnectedSpace X] (x₀ : X)
    (hlocal : ∀ x : X, ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier)
    (γ : C(I, X)) (p : BasedPathFiber x₀ (γ 0)) (t : I) :
    basedPathEndpoint x₀ (basedPathLiftCurve x₀ hlocal γ p t) = γ t := rfl

theorem basedPathLiftCurve_zero [PathConnectedSpace X] [LocallyPathConnectedSpace X] (x₀ : X)
    (hlocal : ∀ x : X, ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier)
    (γ : C(I, X)) (p : BasedPathFiber x₀ (γ 0)) :
    basedPathLiftCurve x₀ hlocal γ p 0 = ⟨γ 0, p⟩ := by
  let : SimplyConnectedSpace I := unitInterval_simplyConnected
  exact basedPathMapLift_at_base x₀ γ 0 p

theorem basedPathLiftCurve_one [PathConnectedSpace X] [LocallyPathConnectedSpace X] (x₀ : X)
    (hlocal : ∀ x : X, ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier)
    (γ : C(I, X)) (p : BasedPathFiber x₀ (γ 0)) :
    basedPathLiftCurve x₀ hlocal γ p 1 =
      ⟨γ 1, p.trans (Path.Homotopic.Quotient.mk (Path.id.map γ.continuous))⟩ := by
  let : SimplyConnectedSpace I := unitInterval_simplyConnected
  have he : Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (0 : I) 1) =
      Path.Homotopic.Quotient.mk Path.id := Subsingleton.elim _ _
  change Bundle.TotalSpace.mk (γ 1) (p.trans ((Path.Homotopic.Quotient.mk
    (PathConnectedSpace.somePath (0 : I) 1)).map γ)) = _
  rw [he]
  rfl

/-- The canonical lifted path has exactly the endpoint given by path-class concatenation. -/
def basedPathLiftPath [PathConnectedSpace X] [LocallyPathConnectedSpace X] (x₀ : X)
    (hlocal : ∀ x : X, ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier)
    {a b : X} (γ : Path a b) (p : BasedPathFiber x₀ a) :
    @Path (BasedPathTotalSpace x₀) (basedPathCoverTopology x₀ hlocal)
      ⟨a, p⟩ ⟨b, p.trans (Path.Homotopic.Quotient.mk γ)⟩ := by
  let : TopologicalSpace (BasedPathTotalSpace x₀) := basedPathCoverTopology x₀ hlocal
  let p₀ := Path.Homotopic.Quotient.cast p rfl γ.source
  refine ⟨basedPathLiftCurve x₀ hlocal γ.toContinuousMap p₀, ?_, ?_⟩
  · change basedPathLiftCurve x₀ hlocal γ.toContinuousMap p₀ 0 = _
    rw [basedPathLiftCurve_zero]
    exact basedPathTotalSpace_mk_cast x₀ γ.source p
  · change basedPathLiftCurve x₀ hlocal γ.toContinuousMap p₀ 1 = _
    rw [basedPathLiftCurve_one]
    have hmap : Path.id.map γ.continuous = γ.cast γ.source γ.target := by ext t; rfl
    rw [hmap, Path.Homotopic.Quotient.mk_cast]
    change Bundle.TotalSpace.mk (γ 1)
      ((Path.Homotopic.Quotient.cast p rfl γ.source).trans
        ((Path.Homotopic.Quotient.mk γ).cast γ.source γ.target)) = _
    rw [pathClass_cast_trans]
    exact basedPathTotalSpace_mk_cast x₀ γ.target _

theorem basedPathLiftPath_endpoint [PathConnectedSpace X] [LocallyPathConnectedSpace X] (x₀ : X)
    (hlocal : ∀ x : X, ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier)
    {a b : X} (γ : Path a b) (p : BasedPathFiber x₀ a) (t : I) :
    basedPathEndpoint x₀ (basedPathLiftPath x₀ hlocal γ p t) = γ t := rfl

theorem basedPathCover_pathConnected [PathConnectedSpace X] [LocallyPathConnectedSpace X] (x₀ : X)
    (hlocal : ∀ x : X, ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier) :
    @PathConnectedSpace (BasedPathTotalSpace x₀) (basedPathCoverTopology x₀ hlocal) := by
  let : TopologicalSpace (BasedPathTotalSpace x₀) := basedPathCoverTopology x₀ hlocal
  let root : BasedPathTotalSpace x₀ := ⟨x₀, Path.Homotopic.Quotient.refl x₀⟩
  have hroot : ∀ z : BasedPathTotalSpace x₀, Joined root z := by
    rintro ⟨x, p⟩
    obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective p
    simpa only [Path.Homotopic.Quotient.refl_trans] using
      (show Joined root ⟨x, (Path.Homotopic.Quotient.refl x₀).trans (Path.Homotopic.Quotient.mk γ)⟩ from
        ⟨basedPathLiftPath x₀ hlocal γ (Path.Homotopic.Quotient.refl x₀)⟩)
  exact { nonempty := ⟨root⟩, joined := fun a b => (hroot a).symm.trans (hroot b) }

/-- Every path in the constructed covering has the endpoint prescribed by concatenation of
its projected path homotopy class. -/
theorem basedPathCover_path_endpointClass [PathConnectedSpace X] [LocallyPathConnectedSpace X] (x₀ : X)
    (hlocal : ∀ x : X, ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier) :
    letI : TopologicalSpace (BasedPathTotalSpace x₀) := basedPathCoverTopology x₀ hlocal
    ∀ {a b : BasedPathTotalSpace x₀} (Γ : Path a b), b.snd = a.snd.trans
      (Path.Homotopic.Quotient.mk (Γ.map (basedPathCover_isCovering x₀ hlocal).continuous)) := by
  let : TopologicalSpace (BasedPathTotalSpace x₀) := basedPathCoverTopology x₀ hlocal
  intro a b Γ
  let hp := basedPathCover_isCovering x₀ hlocal
  let γ : Path a.proj b.proj := Γ.map hp.continuous
  let L := basedPathLiftPath x₀ hlocal γ a.snd
  have heq : (Γ : I → BasedPathTotalSpace x₀) = L := hp.eq_of_comp_eq Γ.continuous L.continuous
    (by funext t; exact (basedPathLiftPath_endpoint x₀ hlocal γ a.snd t).symm) 0
    (Γ.source.trans L.source.symm)
  have hlast : b = (⟨b.proj, a.snd.trans (Path.Homotopic.Quotient.mk γ)⟩ : BasedPathTotalSpace x₀) := by
    exact Γ.target.symm.trans ((congrFun heq 1).trans L.target)
  exact (Bundle.TotalSpace.mk_injective b.proj) hlast

theorem basedPathCover_loop_map_class_eq_refl [PathConnectedSpace X] [LocallyPathConnectedSpace X] (x₀ : X)
    (hlocal : ∀ x : X, ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier) :
    letI : TopologicalSpace (BasedPathTotalSpace x₀) := basedPathCoverTopology x₀ hlocal
    ∀ (a : BasedPathTotalSpace x₀) (Γ : Path a a),
      Path.Homotopic.Quotient.mk (Γ.map (basedPathCover_isCovering x₀ hlocal).continuous) =
        Path.Homotopic.Quotient.refl a.proj := by
  let : TopologicalSpace (BasedPathTotalSpace x₀) := basedPathCoverTopology x₀ hlocal
  intro a Γ
  have he := basedPathCover_path_endpointClass x₀ hlocal Γ
  have hc := congrArg (fun q : Path.Homotopic.Quotient x₀ a.proj =>
    (Path.Homotopic.Quotient.symm a.snd).trans q) he
  dsimp only [basedPathEndpoint] at hc ⊢
  rw [Path.Homotopic.Quotient.symm_trans, ← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans] at hc
  exact hc.symm

/-- The actual constructed covering total space is simply connected. -/
theorem basedPathCover_simplyConnected [PathConnectedSpace X] [LocallyPathConnectedSpace X] (x₀ : X)
    (hlocal : ∀ x : X, ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier) :
    @SimplyConnectedSpace (BasedPathTotalSpace x₀) (basedPathCoverTopology x₀ hlocal) := by
  let : TopologicalSpace (BasedPathTotalSpace x₀) := basedPathCoverTopology x₀ hlocal
  let : PathConnectedSpace (BasedPathTotalSpace x₀) := basedPathCover_pathConnected x₀ hlocal
  refine simply_connected_iff_loops_nullhomotopic.mpr ⟨inferInstance, ?_⟩
  intro a Γ
  apply Path.Homotopic.Quotient.eq.mp
  apply (basedPathCover_isCovering x₀ hlocal).injective_path_homotopic_map a a
  dsimp only
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map]
  have hr : (Path.refl a).map (basedPathCover_isCovering x₀ hlocal).continuous =
      Path.refl a.proj := by ext t; rfl
  rw [hr]
  exact basedPathCover_loop_map_class_eq_refl x₀ hlocal a Γ

/-- Actual open contractible coordinate-disc neighborhoods can be chosen inside any prescribed
open neighborhood on a Riemann atlas. -/
theorem RiemannAtlas.exists_contractible_open_subset {X : Type*} [TopologicalSpace X]
    (A : RiemannAtlas X) (x : X) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ContractibleSpace V := by
  obtain ⟨e, _he, hx⟩ := A.cover x
  have hW : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
  have heW : e x ∈ e.target ∩ e.symm ⁻¹' U :=
    ⟨e.map_source hx, by simpa only [Set.mem_preimage, e.left_inv hx] using hxU⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds heW)
  have hbt : Metric.ball (e x) r ⊆ e.target := fun z hz => (hball hz).1
  let V : Set X := e.symm '' Metric.ball (e x) r
  have hVo : IsOpen V := e.symm.isOpen_image_of_subset_source Metric.isOpen_ball hbt
  have hxV : x ∈ V := ⟨e x, by simpa using hr, e.left_inv hx⟩
  have hVU : V ⊆ U := by
    rintro z ⟨w, hw, rfl⟩
    exact (hball hw).2
  let E : Metric.ball (e x) r ≃ₜ V := e.symm.homeomorphOfImageSubsetSource hbt rfl
  let : ContractibleSpace (Metric.ball (e x) r) := Metric.contractibleSpace_ball hr
  exact ⟨V, hVo, hxV, hVU, E.symm.contractibleSpace⟩

/-- These genuine coordinate neighborhoods are simply connected as spaces, not just connected. -/
theorem RiemannAtlas.exists_simplyConnected_open_subset {X : Type*} [TopologicalSpace X]
    (A : RiemannAtlas X) (x : X) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ SimplyConnectedSpace V := by
  obtain ⟨V, hVo, hxV, hVU, hVc⟩ := A.exists_contractible_open_subset x U hU hxU
  let : ContractibleSpace V := hVc
  exact ⟨V, hVo, hxV, hVU, inferInstance⟩

/-- A Riemann atlas supplies a basis of truly contractible neighborhoods. -/
theorem RiemannAtlas.stronglyLocallyContractibleSpace {X : Type*} [TopologicalSpace X]
    (A : RiemannAtlas X) : StronglyLocallyContractibleSpace X := by
  constructor
  intro x
  rw [Filter.hasBasis_self]
  intro U hU
  obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.mp hU
  obtain ⟨W, hWo, hxW, hWV, hWc⟩ := A.exists_contractible_open_subset x V hVo hxV
  exact ⟨W, hWo.mem_nhds hxW, hWc, hWV.trans hVU⟩

theorem RiemannAtlas.locallyContractibleSpace {X : Type*} [TopologicalSpace X]
    (A : RiemannAtlas X) : LocallyContractibleSpace X := by
  let : StronglyLocallyContractibleSpace X := A.stronglyLocallyContractibleSpace
  exact StronglyLocallyContractibleSpace.locallyContractible


universe u

/-- A genuine simply connected covering Riemann surface, with analytic surjective projection. -/
structure RiemannUniversalCover {S : Type u} [TopologicalSpace S] (R : RiemannSurface S) where
  space : Type u
  topology : TopologicalSpace space
  surface : @RiemannSurface space topology
  simplyConnected : @SimplyConnectedSpace space topology
  projection : space → S
  covering : @IsCoveringMap space S topology _ projection
  surjective : Function.Surjective projection
  analytic_projection : @RiemannAnalyticMap space S topology _ surface.toRiemannAtlas R.toRiemannAtlas projection

theorem RiemannAtlas.basedPathLocalChart_cover [PathConnectedSpace X] (A : RiemannAtlas X)
    (x₀ x : X) : ∃ C : BasedPathLocalChart x₀, x ∈ C.carrier := by
  obtain ⟨U, hU, hxU, _, hSC⟩ := A.exists_simplyConnected_open_subset x Set.univ isOpen_univ (mem_univ x)
  exact ⟨⟨U, hU, hSC, ⟨x, hxU⟩,
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x)⟩, hxU⟩

/--
Every Riemann surface has an actually constructed simply connected
smooth unlimited covering Riemann surface.
-/
theorem riemannSurface_nonempty_universalCover {S : Type u} [TopologicalSpace S] (R : RiemannSurface S) :
    Nonempty (RiemannUniversalCover R) := by
  let : PathConnectedSpace S := R.pathConnectedSpace
  let : LocallyPathConnectedSpace S := R.toRiemannAtlas.locallyPathConnectedSpace
  let x₀ : S := Classical.choice (inferInstance : Nonempty S)
  let hlocal := R.toRiemannAtlas.basedPathLocalChart_cover x₀
  let T := basedPathCoverTopology x₀ hlocal
  let : TopologicalSpace (BasedPathTotalSpace x₀) := T
  have hp : IsCoveringMap (basedPathEndpoint x₀) := basedPathCover_isCovering x₀ hlocal
  have hSC : SimplyConnectedSpace (BasedPathTotalSpace x₀) := basedPathCover_simplyConnected x₀ hlocal
  let : SimplyConnectedSpace (BasedPathTotalSpace x₀) := hSC
  let B := coveringRiemannSurface R (basedPathEndpoint x₀) hp
  refine ⟨⟨BasedPathTotalSpace x₀, T, B, hSC, basedPathEndpoint x₀, hp,
    basedPathEndpoint_surjective x₀, ?_⟩⟩
  exact R.toRiemannAtlas.liftLocalHomeomorph_projection_analytic (basedPathEndpoint x₀) hp.isLocalHomeomorph

theorem RiemannUniversalCover.smoothUnlimited {S : Type u} [TopologicalSpace S] {R : RiemannSurface S}
    (C : RiemannUniversalCover R) : @_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.IsSmoothUnlimitedCovering C.space S C.topology _ C.projection := by
  let : TopologicalSpace C.space := C.topology
  exact _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.covering_isSmoothUnlimited C.covering

theorem RiemannUniversalCover.curve_lift_existsUnique {S : Type u} [TopologicalSpace S]
    {R : RiemannSurface S} (C : RiemannUniversalCover R) (γ : C(I, S)) (y : C.space)
    (hy : γ 0 = C.projection y) :
    ∃! Γ : @ContinuousMap I C.space _ C.topology, C.projection ∘ Γ = γ ∧ Γ 0 = y := by
  let : TopologicalSpace C.space := C.topology
  exact _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.covering_path_lift_existsUnique C.covering γ y hy

end LowDimensionalTopology.Geometry.Surfaces
