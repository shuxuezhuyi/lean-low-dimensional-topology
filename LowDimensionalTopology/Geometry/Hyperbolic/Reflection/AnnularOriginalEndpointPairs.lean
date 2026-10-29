module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularOriginalCuffEndpoints

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open Fuchsian Surfaces

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
  (hin : 1 + r < x) (hout : x + r < E)
local notation "P" => annularPairReflectionHalfPlaneData E r x hE hr hin hout
local notation "D" => HalfPlaneFuchsianGroup.cayleyData P
local notation "hNE" => annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
local notation "hFG" => annularPairReflectionDiscGroup_fg E r x hE hr hin hout
local notation "g" => annularDiscPeripheralWord E r x hE hr hin hout
local notation "S" => annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
local notation "Moriginal" => threeBoundaryQuotientModel D
  (annularPairReflectionDiscGroup_noElliptic E r x hE hr hin hout)
local notation "π" => HyperbolicSurfaceModel.halfPlaneCover Moriginal

/-- The same six actual feet give three different unordered projected mirror-endpoint pairs. -/
theorem annularSixFeet_original_endpointPairs_pairwise_ne
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (D).asFuchsianDisc (g i))
    (hsig : HasNielsenFuchsianSignature D hNE hFG 0 [] 0 3)
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ)
    (h12 : (S 0).OrthogonalAt K12 p12) (h21 : (S 1).OrthogonalAt K12 p21)
    (h23 : (S 1).OrthogonalAt K23 p23) (h32 : (S 2).OrthogonalAt K23 p32)
    (h31 : (S 2).OrthogonalAt K31 p31) (h13 : (S 0).OrthogonalAt K31 p13) :
    let u : Fin 3 → ℍ := ![p12, p21, p32]
    let v : Fin 3 → ℍ := ![p13, p23, p31]
    Pairwise (fun i j =>
      ({π (u i), π (v i)} : Set (MobiusDomainQuotient (D).domain)) ≠
        {π (u j), π (v j)}) := by
  dsimp only
  obtain ⟨q, _hq, hinj, hall, _ht12, _ht31, _ht23,
      hp12, hp21, hp13, hp31, hp23, hp32⟩ :=
    annularSixFeet_original_cuff_endpoints E r x hE hr hin hout hB hsig
      K12 K23 K31 p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13
  have hd := annularOriginalCuffRanges_pairwise_disjoint E r x hE hr hin hout q hinj hall
  have hsep {i j : Fin 3} {a b : ℍ} (hij : i ≠ j)
      (ha : π a ∈ range (q i).curve) (hb : π b ∈ range (q j).curve) : π a ≠ π b := by
    intro he
    exact disjoint_left.mp (hd hij) ha (he.symm ▸ hb)
  have h01 : ({π p12, π p13} : Set (MobiusDomainQuotient (D).domain)) ≠
      {π p21, π p23} := by
    intro he
    have hm : π p13 ∈ ({π p21, π p23} : Set (MobiusDomainQuotient (D).domain)) :=
      he ▸ (by simp)
    simp only [mem_insert_iff, mem_singleton_iff] at hm
    exact hm.elim (hsep (by decide) hp13 hp21) (hsep (by decide) hp13 hp23)
  have h02 : ({π p12, π p13} : Set (MobiusDomainQuotient (D).domain)) ≠
      {π p32, π p31} := by
    intro he
    have hm : π p12 ∈ ({π p32, π p31} : Set (MobiusDomainQuotient (D).domain)) :=
      he ▸ (by simp)
    simp only [mem_insert_iff, mem_singleton_iff] at hm
    exact hm.elim (hsep (by decide) hp12 hp32) (hsep (by decide) hp12 hp31)
  have h12' : ({π p21, π p23} : Set (MobiusDomainQuotient (D).domain)) ≠
      {π p32, π p31} := by
    intro he
    have hm : π p21 ∈ ({π p32, π p31} : Set (MobiusDomainQuotient (D).domain)) :=
      he ▸ (by simp)
    simp only [mem_insert_iff, mem_singleton_iff] at hm
    exact hm.elim (hsep (by decide) hp21 hp32) (hsep (by decide) hp21 hp31)
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
  | exact False.elim (hij rfl)
  | exact h01
  | exact h01.symm
  | exact h02
  | exact h02.symm
  | exact h12'
  | exact h12'.symm

end LowDimensionalTopology.Geometry.Hyperbolic
