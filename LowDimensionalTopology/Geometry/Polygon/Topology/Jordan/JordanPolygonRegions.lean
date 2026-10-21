module
public import LowDimensionalTopology.External.LeanPool.Schoenflies.JordanClosed
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.NativeRegularBoundaryGerms
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon

/-- Two genuine complementary Jordan regions with common frontier have complementary
closures, without any finite polygon or piecewise-linear assumption. -/
theorem jordan_regions_closure_complements {X : Type*} [TopologicalSpace X]
    {I O B : Set X} (hd : Disjoint I O) (hu : I∪O=Bᶜ)
    (hFI : frontier I=B) (hFO : frontier O=B) :
    closure I=Oᶜ ∧closure O=Iᶜ := by
  have hIBC : ∀z,z∈I∪B ↔z∉O := by
    intro z
    have hp : z∈I ∨z∈O ↔z∉B:=by change z∈I∪O ↔z∈Bᶜ;rw [hu]
    have hdis : ¬(z∈I ∧z∈O):=fun h=>Set.disjoint_left.mp hd h.1 h.2
    simp only [mem_union]
    tauto
  have hOBC : ∀z,z∈O∪B ↔z∉I := by
    intro z
    have hp : z∈I ∨z∈O ↔z∉B:=by change z∈I∪O ↔z∈Bᶜ;rw [hu]
    have hdis : ¬(z∈I ∧z∈O):=fun h=>Set.disjoint_left.mp hd h.1 h.2
    simp only [mem_union]
    tauto
  constructor
  · rw [closure_eq_self_union_frontier,hFI]
    exact Set.ext hIBC
  · rw [closure_eq_self_union_frontier,hFO]
    exact Set.ext hOBC

/-- The actual Jordan inside and outside are regular open, derived from the two shared
frontiers rather than assumed as an extra polygon hypothesis. -/
theorem jordan_regions_regular_open {X : Type*} [TopologicalSpace X]
    {I O B : Set X} (hd : Disjoint I O) (hu : I∪O=Bᶜ)
    (hFI : frontier I=B) (hFO : frontier O=B) :
    interior (closure I)=I ∧interior (closure O)=O := by
  obtain ⟨hI,hO⟩:=jordan_regions_closure_complements hd hu hFI hFO
  constructor
  · rw [hI,interior_compl,hO,compl_compl]
  · rw [hO,interior_compl,hI,compl_compl]

/-- The standard actual complex plane as the real Euclidean plane used by the audited
unconditional Jordan theorem. -/
abbrev complexJordanPlaneHomeomorph : ℂ≃ₜSchoenflies.Plane :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph

def IsComplexJordanCurve (C : Set ℂ) : Prop :=
  Schoenflies.IsJordanCurve (complexJordanPlaneHomeomorph '' C)

def complexJordanInside (C : Set ℂ) : Set ℂ :=
  complexJordanPlaneHomeomorph ⁻¹' Schoenflies.inside (complexJordanPlaneHomeomorph '' C)

def complexJordanOutside (C : Set ℂ) : Set ℂ :=
  complexJordanPlaneHomeomorph ⁻¹' Schoenflies.outside (complexJordanPlaneHomeomorph '' C)

/-- Every genuine arbitrary Jordan curve in the actual complex plane determines its
actual open connected complementary regions, both with precisely the original frontier. -/
theorem complexJordan_regions {C : Set ℂ} (hC : IsComplexJordanCurve C) :
    IsOpen (complexJordanInside C) ∧IsOpen (complexJordanOutside C) ∧
    Disjoint (complexJordanInside C) (complexJordanOutside C) ∧
    complexJordanInside C∪complexJordanOutside C=Cᶜ ∧
    IsConnected (complexJordanInside C) ∧IsConnected (complexJordanOutside C) ∧
    frontier (complexJordanInside C)=C ∧frontier (complexJordanOutside C)=C := by
  let e:=complexJordanPlaneHomeomorph
  have hs:=Schoenflies.jordan_curve_theorem hC
  refine ⟨hs.isOpen_inside.preimage e.continuous,hs.isOpen_outside.preimage e.continuous,
    Schoenflies.disjoint_inside_outside.preimage e,?_,
    e.isConnected_preimage.mpr hs.isConnected_inside,e.isConnected_preimage.mpr hs.isConnected_outside,?_,?_⟩
  · change e ⁻¹' Schoenflies.inside (e '' C)∪e ⁻¹' Schoenflies.outside (e '' C)=Cᶜ
    rw [←preimage_union,Schoenflies.inside_union_outside,preimage_compl,e.injective.preimage_image]
  · change frontier (e ⁻¹' Schoenflies.inside (e '' C))=C
    rw [←e.preimage_frontier,hs.frontier_inside,e.injective.preimage_image]
  · change frontier (e ⁻¹' Schoenflies.outside (e '' C))=C
    rw [←e.preimage_frontier,hs.frontier_outside,e.injective.preimage_image]

/-- Genuine arbitrary complex Jordan regions satisfy the regular-open condition needed
for the native original polygon geometry, with no finite/PL or extra separation assumption. -/
theorem complexJordan_regular_open {C : Set ℂ} (hC : IsComplexJordanCurve C) :
    interior (closure (complexJordanInside C))=complexJordanInside C ∧
    interior (closure (complexJordanOutside C))=complexJordanOutside C := by
  obtain ⟨_,_,hd,hu,_,_,hI,hO⟩:=complexJordan_regions hC
  exact jordan_regions_regular_open hd hu hI hO


/-- An actual continuous injective circle in the complex plane is a genuine Jordan curve
for the unconditional audited Jordan separation theorem. -/
theorem isComplexJordanCurve_of_continuous_injective {f : Circle→ℂ}
    (hc : Continuous f) (hinj : Function.Injective f) : IsComplexJordanCurve (range f) := by
  let γ (t : ℝ) : Schoenflies.Plane:=complexJordanPlaneHomeomorph (f (Circle.exp (2*Real.pi*t)))
  have hγc : Continuous γ:=complexJordanPlaneHomeomorph.continuous.comp
    (hc.comp (Circle.exp.continuous.comp (continuous_const.mul continuous_id)))
  have hloop : Schoenflies.IsLoop γ := by
    refine ⟨hγc.continuousOn,?_,?_⟩
    · simp [γ]
    · intro a ha b hb hab
      have he : Circle.exp (2*Real.pi*a)=Circle.exp (2*Real.pi*b):=
        hinj (complexJordanPlaneHomeomorph.injective hab)
      have harg := (Circle.exp_injOn_Ico (a := 0) (b := 2*Real.pi) (by linarith))
        (show 2*Real.pi*a∈Ico 0 (2*Real.pi) by constructor <;>nlinarith [Real.pi_pos,ha.1,ha.2])
        (show 2*Real.pi*b∈Ico 0 (2*Real.pi) by constructor <;>nlinarith [Real.pi_pos,hb.1,hb.2]) he
      nlinarith [Real.pi_pos]
  refine ⟨γ,hloop,Subset.antisymm ?_ ?_⟩
  · rintro z ⟨t,_ht,rfl⟩
    exact ⟨f (Circle.exp (2*Real.pi*t)),mem_range_self _,rfl⟩
  · rintro z ⟨w,⟨u,rfl⟩,rfl⟩
    have hu : u∈Circle.exp '' Icc 0 (2*Real.pi) := by
      rw [show Icc 0 (2*Real.pi)=Icc 0 (0+2*Real.pi) by simp,
        Circle.periodic_exp.image_Icc (by positivity),Circle.exp_surjective.range_eq]
      trivial
    obtain ⟨t,ht,htu⟩:=hu
    refine ⟨t/(2*Real.pi),⟨div_nonneg ht.1 (by positivity),
      (div_le_one (by positivity : 0<2*Real.pi)).mpr ht.2⟩,?_⟩
    have he : 2*Real.pi*(t/(2*Real.pi))=t := by field_simp
    change complexJordanPlaneHomeomorph (f (Circle.exp (2*Real.pi*(t/(2*Real.pi)))))=_
    rw [he,htu]

end LowDimensionalTopology.Geometry.Polygon
