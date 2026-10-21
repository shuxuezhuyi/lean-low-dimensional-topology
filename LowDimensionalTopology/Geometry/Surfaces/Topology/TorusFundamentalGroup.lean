module
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Homotopy.Product
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
@[expose] public section
noncomputable section
namespace LowDimensionalTopology.Geometry.Surfaces

/-- The actual fundamental group of a product is the product of the actual
fundamental groups, by coordinate projection and product of homotopy classes. -/
def fundamentalGroupPiMulEquiv {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i) :
    FundamentalGroup (∀ i, X i) x ≃* ∀ i, FundamentalGroup (X i) (x i) where
  toFun p i := FundamentalGroup.map ⟨fun y => y i, continuous_apply i⟩ x p
  invFun p := .of (Path.Homotopic.pi (fun i => (p i).asHom))
  left_inv p := by
    apply CategoryTheory.End.ext
    change Path.Homotopic.pi (fun i => Path.Homotopic.proj i p.asHom) = p.asHom
    exact Path.Homotopic.pi_proj p.asHom
  right_inv p := by
    funext i
    apply CategoryTheory.End.ext
    change Path.Homotopic.proj i (Path.Homotopic.pi (fun j => (p j).asHom)) = (p i).asHom
    exact Path.Homotopic.proj_pi i (fun j => (p j).asHom)
  map_mul' p q := by
    funext i
    exact (FundamentalGroup.map ⟨fun y => y i, continuous_apply i⟩ x).map_mul p q

def piFinTwoMulEquiv (G : Type*) [Mul G] : (Fin 2 → G) ≃* G × G where
  toEquiv := finTwoArrowEquiv G
  map_mul' _ _ := rfl

/-- The real two-torus has the genuine fundamental group Z x Z, at every basepoint. -/
def torusFundamentalGroupEquiv (x : Fin 2 → AddCircle (1 : ℝ)) :
    FundamentalGroup (Fin 2 → AddCircle (1 : ℝ)) x ≃* Multiplicative ℤ × Multiplicative ℤ := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  exact (fundamentalGroupPiMulEquiv x).trans
    ((MulEquiv.piCongrRight (fun i => AddCircle.windingNumberIso (x i))).trans
      (piFinTwoMulEquiv (Multiplicative ℤ)))

theorem torusFundamentalGroup_commute (x : Fin 2 → AddCircle (1 : ℝ))
    (p q : FundamentalGroup (Fin 2 → AddCircle (1 : ℝ)) x) : Commute p q := by
  change p * q = q * p
  apply (torusFundamentalGroupEquiv x).injective
  rw [map_mul, map_mul, mul_comm]

theorem torusFundamentalGroup_not_isCyclic (x : Fin 2 → AddCircle (1 : ℝ)) :
    ¬IsCyclic (FundamentalGroup (Fin 2 → AddCircle (1 : ℝ)) x) := by
  intro h
  exact not_isCyclic_prod_of_infinite_nontrivial (Multiplicative ℤ) (Multiplicative ℤ)
    ((torusFundamentalGroupEquiv x).isCyclic.mp h)

/-- A genuine homeomorphism induces an isomorphism of the actual based fundamental groups. -/
def fundamentalGroupHomeomorphMulEquiv {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e.toHomotopyEquiv).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk x)

/-- Cartesian products of actual based fundamental groups. -/
def fundamentalGroupProdMulEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) ≃* FundamentalGroup X x × FundamentalGroup Y y where
  toFun p := (FundamentalGroup.map ⟨Prod.fst, continuous_fst⟩ (x, y) p,
    FundamentalGroup.map ⟨Prod.snd, continuous_snd⟩ (x, y) p)
  invFun p := .of (Path.Homotopic.prod p.1.asHom p.2.asHom)
  left_inv p := by
    apply CategoryTheory.End.ext
    change Path.Homotopic.prod (Path.Homotopic.projLeft p.asHom)
      (Path.Homotopic.projRight p.asHom) = p.asHom
    exact Path.Homotopic.prod_projLeft_projRight p.asHom
  right_inv p := by
    apply Prod.ext
    · apply CategoryTheory.End.ext
      change Path.Homotopic.projLeft (Path.Homotopic.prod p.1.asHom p.2.asHom) = p.1.asHom
      exact Path.Homotopic.projLeft_prod p.1.asHom p.2.asHom
    · apply CategoryTheory.End.ext
      change Path.Homotopic.projRight (Path.Homotopic.prod p.1.asHom p.2.asHom) = p.2.asHom
      exact Path.Homotopic.projRight_prod p.1.asHom p.2.asHom
  map_mul' p q := Prod.ext
    ((FundamentalGroup.map ⟨Prod.fst, continuous_fst⟩ (x, y)).map_mul p q)
    ((FundamentalGroup.map ⟨Prod.snd, continuous_snd⟩ (x, y)).map_mul p q)

def torusProductFundamentalGroupEquiv (x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :
    FundamentalGroup (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) x ≃*
      Multiplicative ℤ × Multiplicative ℤ := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  exact (fundamentalGroupProdMulEquiv x.1 x.2).trans
    ((AddCircle.windingNumberIso x.1).prodCongr (AddCircle.windingNumberIso x.2))

theorem torusProductFundamentalGroup_commute (x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ))
    (p q : FundamentalGroup (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) x) : Commute p q := by
  change p * q = q * p
  apply (torusProductFundamentalGroupEquiv x).injective
  rw [map_mul, map_mul, mul_comm]

theorem torusProductFundamentalGroup_not_isCyclic
    (x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :
    ¬IsCyclic (FundamentalGroup (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) x) := by
  intro h
  exact not_isCyclic_prod_of_infinite_nontrivial (Multiplicative ℤ) (Multiplicative ℤ)
    ((torusProductFundamentalGroupEquiv x).isCyclic.mp h)

end LowDimensionalTopology.Geometry.Surfaces
