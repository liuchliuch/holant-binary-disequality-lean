import Holant.Certificates.PlatonicIncidence.IncidenceTransport

/-! Kernel deletion on the literal projective domain, not merely its finite
index presentation. Adjacency means sharing a rich actual complex line. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

local instance : DecidableEq DomainPoint := Classical.decEq _
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def matrixPoint (U : Fin n→Mat) (hU : ∀i,U i≠0) (i : Fin n) : DomainPoint :=
  Projectivization.mk ℂ (U i) (hU i)

def projectiveDictionary (U : Fin n→Mat) (hU : ∀i,U i≠0) : Finset DomainPoint := by
  classical
  exact Finset.univ.image (matrixPoint U hU)

def matrixIntersection (U : Fin n→Mat) (W : Submodule ℂ Mat) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => U i∈W

@[simp] theorem mem_matrixIntersection (U : Fin n→Mat) (W : Submodule ℂ Mat) (i : Fin n) :
    i∈matrixIntersection U W ↔ U i∈W := by
  classical
  simp [matrixIntersection]

def projectiveGraph (U : Fin n→Mat) : SimpleGraph DomainPoint where
  Adj p q := p≠q ∧ ∃L : Submodule ℂ Mat,Module.finrank ℂ L=2 ∧
    3≤(matrixIntersection U L).card ∧ p∈L.projectivization ∧ q∈L.projectivization
  symm := ⟨by
    rintro p q ⟨hne,L,hd,hc,hp,hq⟩
    exact ⟨hne.symm,L,hd,hc,hq,hp⟩⟩
  loopless := ⟨by intro p h; exact h.1 rfl⟩

theorem matrixPoint_injective (U : Fin n→Mat) (hU : ∀i,U i≠0)
    (hfaith : ∀(i j : Fin n) (c : ℂ),U i=c • U j→i=j) : Function.Injective (matrixPoint U hU) := by
  intro i j h
  obtain ⟨c,_,hc⟩ := (proportional_point_iff _ _ _ _).mpr h
  exact hfaith i j c hc

/-- The finite index count used by projectiveGraph is exactly the number of
distinct actual projective domain points in the subspace. -/
theorem projective_intersection_card (U : Fin n→Mat) (hU : ∀i,U i≠0)
    (hfaith : ∀(i j : Fin n) (c : ℂ),U i=c • U j→i=j) (W : Submodule ℂ Mat) :
    ((projectiveDictionary U hU).filter (fun p => p∈W.projectivization)).card=
      (matrixIntersection U W).card := by
  classical
  have he : (projectiveDictionary U hU).filter (fun p => p∈W.projectivization)=
      (matrixIntersection U W).image (matrixPoint U hU) := by
    ext p
    simp only [projectiveDictionary,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨i,rfl⟩,hi⟩
      exact ⟨i,(mem_matrixIntersection U W i).mpr
        ((Submodule.mk_mem_projectivization_iff W (hU i)).mp hi),rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,rfl⟩,(Submodule.mk_mem_projectivization_iff W (hU i)).mpr
        ((mem_matrixIntersection U W i).mp hi)⟩
  rw [he,Finset.card_image_of_injective _ (matrixPoint_injective U hU hfaith)]

theorem projectiveGraph_actual_adjacency (U : Fin n→Mat) (hU : ∀i,U i≠0)
    (hfaith : ∀(i j : Fin n) (c : ℂ),U i=c • U j→i=j) (p q : DomainPoint) :
    (projectiveGraph U).Adj p q ↔ p≠q ∧ ∃L : Submodule ℂ Mat,
      Module.finrank ℂ L=2 ∧
      3≤((projectiveDictionary U hU).filter (fun z => z∈L.projectivization)).card ∧
      p∈L.projectivization ∧ q∈L.projectivization := by
  simp only [projective_intersection_card U hU hfaith]
  rfl

theorem matrix_pair_dimension (U : Fin n→Mat) (hU : ∀i,U i≠0)
    (hfaith : ∀(i j : Fin n) (c : ℂ),U i=c • U j→i=j) (i j : Fin n) (hij : i≠j) :
    Module.finrank ℂ (Submodule.span ℂ ({U i,U j} : Set Mat))=2 := by
  have hli : LinearIndependent ℂ ![U i,U j] :=
    (Projectivization.independent_mk_iff_LinearIndependent _ _).mp
      ((Projectivization.independent_pair_iff_ne _ _).mpr
        (fun h => hij (matrixPoint_injective U hU hfaith h)))
  rw [←Matrix.range_cons_cons_empty (U i) (U j) ![]]
  simpa using finrank_span_eq_card hli

theorem matrix_projective_adjacency (U : Fin n→Mat) (hU : ∀i,U i≠0)
    (hfaith : ∀(i j : Fin n) (c : ℂ),U i=c • U j→i=j) (i j : Fin n)
    (hij : (matrixGraph U).Adj i j) :
    (projectiveGraph U).Adj (matrixPoint U hU i) (matrixPoint U hU j) := by
  obtain ⟨hne,S,⟨a,b,hab,hS⟩,hc,hi,hj⟩ := hij
  let L := Submodule.span ℂ ({U a,U b} : Set Mat)
  have he : matrixIntersection U L=S := Finset.ext (fun k => (mem_matrixIntersection U L k).trans (hS k).symm)
  refine ⟨fun h => hne (matrixPoint_injective U hU hfaith h),L,
    matrix_pair_dimension U hU hfaith a b hab,?_,?_,?_⟩
  · rwa [he]
  · exact (Submodule.mk_mem_projectivization_iff L (hU i)).mpr ((hS i).mp hi)
  · exact (Submodule.mk_mem_projectivization_iff L (hU j)).mpr ((hS j).mp hj)

def projectiveDeleted (U : Fin n→Mat) (hU : ∀i,U i≠0) (W : Submodule ℂ Mat) : Set DomainPoint :=
  {p | p∈projectiveDictionary U hU ∧ p∉W.projectivization}

def deletionPointHom (U : Fin n→Mat) (hU : ∀i,U i≠0)
    (hfaith : ∀(i j : Fin n) (c : ℂ),U i=c • U j→i=j) (W : Submodule ℂ Mat) :
    (matrixGraph U).induce {i | U i∉W} →g (projectiveGraph U).induce (projectiveDeleted U hU W) where
  toFun i := ⟨matrixPoint U hU i.val,by
    constructor
    · exact Finset.mem_image.mpr ⟨i.val,Finset.mem_univ _,rfl⟩
    · exact fun h => i.property ((Submodule.mk_mem_projectivization_iff W (hU i.val)).mp h)⟩
  map_rel' h := matrix_projective_adjacency U hU hfaith _ _ h

theorem deletionPointHom_surjective (U : Fin n→Mat) (hU : ∀i,U i≠0)
    (hfaith : ∀(i j : Fin n) (c : ℂ),U i=c • U j→i=j) (W : Submodule ℂ Mat) :
    Function.Surjective (deletionPointHom U hU hfaith W) := by
  intro p
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp p.property.1
  have hn : U i∉W := by
    intro h
    apply p.property.2
    rw [←hi]
    exact (Submodule.mk_mem_projectivization_iff W (hU i)).mpr h
  refine ⟨⟨i,hn⟩,Subtype.ext ?_⟩
  exact hi

theorem projective_connected_of_matrix_connected (U : Fin n→Mat) (hU : ∀i,U i≠0)
    (hfaith : ∀(i j : Fin n) (c : ℂ),U i=c • U j→i=j) (W : Submodule ℂ Mat)
    (hc : ((matrixGraph U).induce {i | U i∉W}).Connected) :
    ((projectiveGraph U).induce (projectiveDeleted U hU W)).Connected :=
  hc.map (deletionPointHom U hU hfaith W) (deletionPointHom_surjective U hU hfaith W)

theorem transformed_representative_nonzero (g : PlatonicModel) (e : Mat ≃ₗ[ℂ] Mat)
    (i : Fin (size g)) : e (representative g i)≠0 := by
  intro h
  apply representative_ne_zero g i
  apply e.injective
  simpa only [map_zero] using h

theorem transformed_representative_faithful (g : PlatonicModel) (e : Mat ≃ₗ[ℂ] Mat)
    (i j : Fin (size g)) (c : ℂ) (h : e (representative g i)=c • e (representative g j)) : i=j := by
  apply projectively_injective g i j c
  apply e.injective
  simpa only [map_smul] using h

/-- Source A.20(iii), on actual complex projective points. Its `Connected`
conclusion contains nonemptiness, including every dimension0/1/2 deletion. -/
theorem actual_kernel_deleted_connected (g : PlatonicModel) (e : Mat ≃ₗ[ℂ] Mat)
    (W : Submodule ℂ Mat) (hW : Module.finrank ℂ W≤2) :
    ((projectiveGraph (fun i => e (representative g i))).induce
      (projectiveDeleted (fun i => e (representative g i))
        (transformed_representative_nonzero g e) W)).Connected :=
  projective_connected_of_matrix_connected _ (transformed_representative_nonzero g e)
    (transformed_representative_faithful g e) W (transformed_kernel_deleted_connected g e W hW)

end
end Holant.Certificates.PlatonicIncidence
