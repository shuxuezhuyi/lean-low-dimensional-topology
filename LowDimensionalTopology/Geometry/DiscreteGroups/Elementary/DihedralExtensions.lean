/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

@[expose] public section
noncomputable section
namespace LowDimensionalTopology.Geometry.DiscreteGroups

def dihedralExtensionHom {G : Type*} [Group G] (n : ℕ)
    (c : Multiplicative (ZMod n) →* G) (s : G) (hs : s*s = 1)
    (hi : ∀ i : ZMod n, c (Multiplicative.ofAdd i)*s =
      s*c (Multiplicative.ofAdd (-i))) : DihedralGroup n →* G where
  toFun x := match x with
    | .r i => c (Multiplicative.ofAdd i)
    | .sr i => s*c (Multiplicative.ofAdd i)
  map_one' := by
    change c 1 = 1
    exact map_one c
  map_mul' x y := by
    have hadd (i j : ZMod n) :
        c (Multiplicative.ofAdd (i+j)) =
          c (Multiplicative.ofAdd i)*c (Multiplicative.ofAdd j) := map_mul c _ _
    cases x with
    | r i =>
      cases y with
      | r j => exact hadd i j
      | sr j =>
        change s*c (Multiplicative.ofAdd (j-i)) =
          c (Multiplicative.ofAdd i)*(s*c (Multiplicative.ofAdd j))
        rw [← mul_assoc,hi,mul_assoc,← hadd]
        simp only [sub_eq_add_neg,add_comm]
    | sr i =>
      cases y with
      | r j =>
        change s*c (Multiplicative.ofAdd (i+j)) =
          (s*c (Multiplicative.ofAdd i))*c (Multiplicative.ofAdd j)
        rw [hadd,mul_assoc]
      | sr j =>
        change c (Multiplicative.ofAdd (j-i)) =
          (s*c (Multiplicative.ofAdd i))*(s*c (Multiplicative.ofAdd j))
        rw [mul_assoc,← mul_assoc (c (Multiplicative.ofAdd i)),hi]
        simp only [mul_assoc]
        rw [← mul_assoc s s,hs,one_mul,← hadd]
        simp only [sub_eq_add_neg,add_comm]

theorem dihedralExtensionHom_surjective {G : Type*} [Group G] (n : ℕ)
    (c : Multiplicative (ZMod n) →* G) (s : G) (hs : s*s = 1)
    (hi : ∀ i : ZMod n,c (Multiplicative.ofAdd i)*s=s*c (Multiplicative.ofAdd (-i)))
    (hcover : ∀ g : G,(∃ i : ZMod n,g=c (Multiplicative.ofAdd i)) ∨
      ∃ i : ZMod n,g=s*c (Multiplicative.ofAdd i)) :
    Function.Surjective (dihedralExtensionHom n c s hs hi) := by
  intro g
  rcases hcover g with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · exact ⟨.r i,rfl⟩
  · exact ⟨.sr i,rfl⟩

def dihedralExtensionEquiv {G : Type*} [Group G] (n : ℕ) [NeZero n]
    (c : Multiplicative (ZMod n) →* G) (s : G) (hs : s*s = 1)
    (hi : ∀ i : ZMod n,c (Multiplicative.ofAdd i)*s=s*c (Multiplicative.ofAdd (-i)))
    (hcover : ∀ g : G,(∃ i : ZMod n,g=c (Multiplicative.ofAdd i)) ∨
      ∃ i : ZMod n,g=s*c (Multiplicative.ofAdd i))
    (hcard : Nat.card G = 2*n) : DihedralGroup n ≃* G :=
  MulEquiv.ofBijective (dihedralExtensionHom n c s hs hi)
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨dihedralExtensionHom_surjective n c s hs hi hcover,by
        rw [Nat.card_eq_fintype_card,DihedralGroup.card,hcard]⟩)

def cyclicIndexTwoDihedralEquiv {G : Type*} [Group G]
    (K : Subgroup G) [Finite K] [IsCyclic K] (s : G) (hs : s*s=1)
    (hi : ∀ k : K,k.val*s=s*k.val⁻¹)
    (hcover : ∀ g : G,g ∈ K ∨ ∃ k : K,g=s*k.val)
    (hcard : Nat.card G=2*Nat.card K) : DihedralGroup (Nat.card K) ≃* G := by
  let e : Multiplicative (ZMod (Nat.card K)) ≃* K := zmodCyclicMulEquiv inferInstance
  let c : Multiplicative (ZMod (Nat.card K)) →* G := K.subtype.comp e.toMonoidHom
  have hcomm (i : ZMod (Nat.card K)) : c (Multiplicative.ofAdd i)*s =
      s*c (Multiplicative.ofAdd (-i)) := by
    have hneg : c (Multiplicative.ofAdd (-i)) = (c (Multiplicative.ofAdd i))⁻¹ :=
      map_inv c (Multiplicative.ofAdd i)
    rw [hneg]
    exact hi (e (Multiplicative.ofAdd i))
  have hcov (g : G) : (∃ i : ZMod (Nat.card K),g=c (Multiplicative.ofAdd i)) ∨
      ∃ i : ZMod (Nat.card K),g=s*c (Multiplicative.ofAdd i) := by
    rcases hcover g with hg | ⟨k,hk⟩
    · refine Or.inl ⟨Multiplicative.toAdd (e.symm ⟨g,hg⟩),?_⟩
      change g = (e (e.symm ⟨g,hg⟩)).val
      rw [e.apply_symm_apply]
    · refine Or.inr ⟨Multiplicative.toAdd (e.symm k),?_⟩
      change g = s*(e (e.symm k)).val
      rw [e.apply_symm_apply]
      exact hk
  exact dihedralExtensionEquiv (Nat.card K) c s hs hcomm hcov hcard

end LowDimensionalTopology.Geometry.DiscreteGroups
