import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPolynomials
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralRanks
import Holant.Certificates.PlatonicIncidence.Subspaces

/-! Coefficient extraction from the preserved marked-octahedral proof. Arbitrary rank-two preservers, not a proposed finite
map atlas. Both actual image planes get root-pair bases and literal O
secant receipts. The finite cells below contain explicit column linear
equations and the previously proved exact two-sided polynomial equations.
Completeness of the eighteen four-lines/eight harmonic maps is NOT assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator Holant.Certificates.RainbowOrbit
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open scoped BigOperators Matrix

def rootIndices (f : Form) (W : Submodule ℂ V) : Finset (Fin 24) := by
  classical
  exact Finset.univ.filter (fun k => point f k ∈ W)

@[simp] theorem mem_rootIndices (f : Form) (W : Submodule ℂ V) (k : Fin 24) :
    k ∈ rootIndices f W ↔ point f k ∈ W := by
  classical
  simp [rootIndices]

/-- Pure coefficient pull. It is never used as a physical vertex. -/
def coefficientPull (f : Form) : V →ₗ[ℂ] PlatonicIncidence.Mat where
  toFun v := complexPull f (assemble v)
  map_add' v w := by
    change complexPull f (coordinates.symm (v+w)) =
      complexPull f (coordinates.symm v)+complexPull f (coordinates.symm w)
    rw [map_add]
    simp [complexPull,Matrix.mul_add,Matrix.add_mul]
  map_smul' c v := by
    change complexPull f (coordinates.symm (c • v)) = c • complexPull f (coordinates.symm v)
    rw [map_smul]
    exact complexPull_smul f c _

theorem coefficientPull_injective (f : Form) : Function.Injective (coefficientPull f) := by
  intro v w h
  have hh := congrArg (complexTheta f) h
  simp only [coefficientPull,LinearMap.coe_mk,AddHom.coe_mk,complexTheta_complexPull] at hh
  exact coordinates.symm.injective hh

/-- The original root index is preserved by the old literal source table. -/
theorem coefficientPull_point (f : Form) (k : Fin 24) :
    coefficientPull f (point f k) = representative .octahedral k := by
  change complexPull f (assemble (quaternionCoefficient
    (complexMatrix (theta f (OctahedralSeparator.standard k))))) = goldenMatrix (octahedralRaw k)
  rw [assemble_coefficient,complexMatrix_theta,complexPull_complexTheta]
  exact (octahedralRaw_standard k).symm

theorem rootIndices_pull (f : Form) (W : Submodule ℂ V) :
    rootIndices f W = deletion .octahedral (W.map (coefficientPull f)) := by
  ext k
  rw [mem_rootIndices,mem_deletion]
  constructor
  · intro hk
    exact ⟨point f k,hk,coefficientPull_point f k⟩
  · rintro ⟨v,hv,he⟩
    have hh : v = point f k := (coefficientPull_injective f)
      (he.trans (coefficientPull_point f k).symm)
    exact hh ▸ hv

theorem rootIndices_bound (f : Form) (W : Submodule ℂ V)
    (hW : Module.finrank ℂ W ≤ 2) : (rootIndices f W).card ≤ 4 := by
  have he := (Submodule.equivMapOfInjective (coefficientPull f)
    (coefficientPull_injective f) W).finrank_eq
  have hd : Module.finrank ℂ (W.map (coefficientPull f)) ≤ 2 := he ▸ hW
  rw [rootIndices_pull]
  exact deletion_bound .octahedral _ hd

theorem span_root_range (f : Form) (A : End) (hA : OneSided (Roots f) A) :
    Submodule.span ℂ (Set.range
      (fun k : {k : Fin 24 // point f k ∈ LinearMap.range A.mulVecLin} => point f k.val)) =
      LinearMap.range A.mulVecLin := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    exact k.property
  · conv_lhs => rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    have hh := hA _ (roots_axis f j)
    rw [Matrix.mulVec_single_one] at hh
    rcases hh with hz | hm
    · rw [hz]
      exact Submodule.zero_mem _
    · obtain ⟨k,c,hc,he⟩ := (roots_iff f _).mp hm
      have hk : point f k ∈ LinearMap.range A.mulVecLin := by
        refine ⟨c⁻¹ • Pi.single j 1,?_⟩
        change A *ᵥ (c⁻¹ • Pi.single j 1) = point f k
        rw [Matrix.mulVec_smul,Matrix.mulVec_single_one,he,smul_smul,inv_mul_cancel₀ hc,one_smul]
      rw [he]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k,hk⟩,rfl⟩)

/-- A real root-pair basis is extracted from the arbitrary actual range. -/
theorem range_root_pair (f : Form) (A : End) (hA : OneSided (Roots f) A) (hr : A.rank = 2) :
    ∃ u : Fin 2 → Fin 24, LinearIndependent ℂ (fun i => point f (u i)) ∧
      (∀ i,point f (u i) ∈ LinearMap.range A.mulVecLin) ∧
      Submodule.span ℂ (Set.range (fun i => point f (u i))) = LinearMap.range A.mulVecLin := by
  classical
  let D := {k : Fin 24 // point f k ∈ LinearMap.range A.mulVecLin}
  let v : D → V := fun k => point f k.val
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℂ v
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = 2 := by
    rw [←finrank_span_eq_card hli,hspan]
    change Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = 2
    rw [show Submodule.span ℂ (Set.range v) = LinearMap.range A.mulVecLin
      from span_root_range f A hA]
    exact hr
  let e : Fin 2 ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (a (e i)).val,hli.comp e e.injective,fun i => (a (e i)).property,?_⟩
  have he : Set.range (fun i : Fin 2 => point f (a (e i)).val) = Set.range (v ∘ a) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨e i,rfl⟩
    · rintro ⟨i,rfl⟩
      obtain ⟨j,rfl⟩ := e.surjective i
      exact ⟨j,rfl⟩
  rw [he,hspan]
  exact span_root_range f A hA

/-- Complete secant coverage for the actual current row's image plane.
This uses the old O incidence completeness, including two/three-point
secants; it does not silently discard them as rank-two impossible. -/
theorem range_secant (f : Form) (A : End) (hA : OneSided (Roots f) A) (hr : A.rank = 2) :
    ∃ t : Fin (secantCount .octahedral),
      rootIndices f (LinearMap.range A.mulVecLin) = globalLine .octahedral t := by
  classical
  obtain ⟨u,hu,hm,_⟩ := range_root_pair f A hA hr
  have hij : u 0 ≠ u 1 := by
    intro he
    have hh := hu.injective (congrArg (point f) he)
    norm_num at hh
  have htwo : 2 ≤ (rootIndices f (LinearMap.range A.mulVecLin)).card := by
    have hh := Finset.one_lt_card.mpr
      ⟨u 0,(mem_rootIndices _ _ _).mpr (hm 0),u 1,(mem_rootIndices _ _ _).mpr (hm 1),hij⟩
    omega
  have he := (Submodule.equivMapOfInjective (coefficientPull f)
    (coefficientPull_injective f) (LinearMap.range A.mulVecLin)).finrank_eq
  have hd : Module.finrank ℂ ((LinearMap.range A.mulVecLin).map (coefficientPull f)) ≤ 2 := by
    rw [←he]
    exact hr.le
  rcases deletion_classification .octahedral _ hd with h | ⟨t,ht⟩
  · rw [←rootIndices_pull] at h
    omega
  · exact ⟨t,(rootIndices_pull _ _).trans ht⟩

abbrev PairCode := Fin 2 → Fin 24
abbrev CellCode := PairCode × PairCode
def rootPlane (f : Form) (u : PairCode) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range (fun i => point f (u i)))

/-- Literal finite linear equations for all four columns; the coefficient
vectors are derived mathematical witnesses, not a desired map oracle. -/
def ColumnEquations (f : Form) (u : PairCode) (A : End) : Prop :=
  ∀ j : Fin 4, ∃ c : Fin 2 → ℂ, ∀ i : Fin 4,
    A i j = ∑ k : Fin 2, c k*point f (u k) i

theorem columns_of_range (f : Form) (u : PairCode) (A : End)
    (h : LinearMap.range A.mulVecLin = rootPlane f u) : ColumnEquations f u A := by
  intro j
  have hj : (fun i => A i j) ∈ rootPlane f u := by
    rw [←h]
    exact ⟨Pi.single j 1,Matrix.mulVec_single_one A j⟩
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hj
  refine ⟨c,?_⟩
  intro i
  have hh := congrFun hc i
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hh.symm

structure Cell (f : Form) (d : CellCode) (A : End) : Prop where
  leftIndependent : LinearIndependent ℂ (fun i => point f (d.1 i))
  rightIndependent : LinearIndependent ℂ (fun i => point f (d.2 i))
  leftRange : LinearMap.range A.mulVecLin = rootPlane f d.1
  rightRange : LinearMap.range (sharp A).mulVecLin = rootPlane f d.2
  leftColumns : ColumnEquations f d.1 A
  rightColumns : ColumnEquations f d.2 (sharp A)
  polynomials : Equations f A
  rank : A.rank = 2

/-- A real, two-way finite cell reduction of arbitrary complex rank-two
preservers. Solving the surviving cells to the 2592 harmonic orbit remains
a further mathematical obligation, not an input to this theorem. -/
theorem rank_two_iff_cells (f : Form) (A : End) :
    TwoSided (Roots f) A ∧ A.rank = 2 ↔ ∃ d : CellCode, Cell f d A := by
  constructor
  · rintro ⟨h,hr⟩
    obtain ⟨u,hu,hm,hspan⟩ := range_root_pair f A h.1 hr
    obtain ⟨v,hv,hvm,hvspan⟩ := range_root_pair f (sharp A) h.2 (by rw [rank_sharp,hr])
    have hU : LinearMap.range A.mulVecLin = rootPlane f u := hspan.symm
    have hV : LinearMap.range (sharp A).mulVecLin = rootPlane f v := hvspan.symm
    exact ⟨(u,v),hu,hv,hU,hV,columns_of_range f u A hU,
      columns_of_range f v (sharp A) hV,(twoSided_iff_equations f A).mp h,hr⟩
  · rintro ⟨d,h⟩
    exact ⟨(twoSided_iff_equations f A).mpr h.polynomials,h.rank⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo
