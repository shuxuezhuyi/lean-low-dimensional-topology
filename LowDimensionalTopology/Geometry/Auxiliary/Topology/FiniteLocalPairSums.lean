module
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
open Filter Topology
namespace LowDimensionalTopology.Geometry.Auxiliary.Topology
/-- A genuine finite involutive pairing with a fixed local pair sum forces its entire
finite sum to be locally constant, without selecting representatives or assuming parity. -/
theorem finite_local_pair_sum_constant {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (mate : ι→ι) (hinv : Function.Involutive mate) (w : ι→X→ℝ) (x : X) (c : ℝ)
    (hpair : ∀i,∀ᶠy in 𝓝 x,w i y+w (mate i) y=c) :
    ∀ᶠy in 𝓝 x,(∑i,w i y)=∑i,w i x := by
  classical
  have hsum (y : X) (hy : ∀i,w i y+w (mate i) y=c) :
      2*(∑i,w i y)=(Fintype.card ι : ℝ)*c := by
    have he := hinv.bijective.sum_comp (fun i=>w i y)
    calc
      2*(∑i,w i y)=(∑i,w i y)+(∑i,w (mate i) y) := by rw [he];ring
      _=∑i,(w i y+w (mate i) y) := by rw [Finset.sum_add_distrib]
      _=∑_i : ι,c := Finset.sum_congr rfl (fun i _=>hy i)
      _=(Fintype.card ι : ℝ)*c := by simp
  have hx : ∀i,w i x+w (mate i) x=c := fun i=>(hpair i).self_of_nhds
  filter_upwards [Filter.eventually_all.mpr hpair] with y hy
  linarith [hsum y hy,hsum x hx]
/-- A finite actual family remains locally constant when its exceptional labels are
in bijection with a finite involutively paired family and every other label is stable. -/
theorem finite_local_sum_constant_of_paired_labels {X ι α : Type*}
    [TopologicalSpace X] [Fintype α] (I : Finset ι) (label : α→ι)
    (hinj : Function.Injective label) (hI : ∀a,label a∈I)
    (mate : α→α) (hinv : Function.Involutive mate) (w : ι→X→ℝ) (x : X) (c : ℝ)
    (hpair : ∀a,∀ᶠy in 𝓝 x,w (label a) y+w (label (mate a)) y=c)
    (hStable : ∀i∈I,i∉Set.range label → ∀ᶠy in 𝓝 x,w i y=w i x) :
    ∀ᶠy in 𝓝 x,(∑i∈I,w i y)=∑i∈I,w i x := by
  classical
  let B:=Finset.univ.image label
  have hBI : B⊆I := by
    intro i hi
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hi
    exact hI a
  have hBSum (y : X) : (∑i∈B,w i y)=∑a,w (label a) y := by
    exact Finset.sum_image (fun _ _ _ _ h=>hinj h)
  have hb:=finite_local_pair_sum_constant mate hinv (fun a=>w (label a)) x c hpair
  have hr : ∀i∈I\B,∀ᶠy in 𝓝 x,w i y=w i x := by
    intro i hi
    rcases Finset.mem_sdiff.mp hi with ⟨hiI,hiB⟩
    apply hStable i hiI
    rintro ⟨a,rfl⟩
    exact hiB (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  filter_upwards [hb,(I\B).eventually_all.mpr hr] with y hy hrest
  calc
    (∑i∈I,w i y)=(∑i∈I\B,w i y)+∑i∈B,w i y := (Finset.sum_sdiff hBI).symm
    _=(∑i∈I\B,w i x)+∑i∈B,w i x := by
      rw [hBSum y,hBSum x,hy]
      congr 1
      exact Finset.sum_congr rfl hrest
    _=∑i∈I,w i x := Finset.sum_sdiff hBI

end LowDimensionalTopology.Geometry.Auxiliary.Topology
