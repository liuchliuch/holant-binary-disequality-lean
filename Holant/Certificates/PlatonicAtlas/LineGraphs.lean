import Holant.Certificates.PlatonicAtlas.LineGraphCertificate
import Holant.Certificates.PlatonicIncidence.DomainGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The source rich-line intersection graphs, interpreted as all actual
complex domain secants, with explicit finite spanning paths. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem richSet_injective (g : PlatonicModel) : Function.Injective (richSet g) := by
  intro i j h
  rw [(rich_rows g i).1,(rich_rows g j).1] at h
  exact richIndex_injective g (globalLine_injective g h)

 theorem richSet_semantics (g : PlatonicModel) (i : Fin (richCount g)) :
    DomainSecant g (richSet g i) ∧ 3≤(richSet g i).card := by
  refine ⟨?_,(rich_rows g i).2.1⟩
  rw [(rich_rows g i).1]
  exact globalLine_semantics g _

 theorem richSet_complete (g : PlatonicModel) (S : Finset (Fin (size g)))
    (hS : DomainSecant g S) (hc : 3≤S.card) : ∃i,richSet g i=S := by
  obtain ⟨t,_,rfl⟩ := Finset.mem_map.mp ((domainLines_exact g S).mpr hS)
  refine ⟨richLookup g t,?_⟩
  rw [(rich_rows g _).1,rich_cover g t hc]
  rfl

 def lineGraph (g : PlatonicModel) : SimpleGraph (Fin (richCount g)) where
  Adj i j := i≠j ∧ (richSet g i∩richSet g j).Nonempty
  symm := ⟨fun i j h => ⟨Ne.symm h.1,by simpa only [Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

 instance (g : PlatonicModel) : DecidableRel (lineGraph g).Adj :=
  fun i j => inferInstanceAs (Decidable (i≠j ∧ (richSet g i∩richSet g j).Nonempty))

 theorem lineGraph_adjacency (g : PlatonicModel) (i j : Fin (richCount g)) :
    (lineGraph g).Adj i j ↔ j∈richNeighbors g i :=
  ((rich_rows g i).2.2.1 j).symm

 theorem lineGraph_degree (g : PlatonicModel) (i : Fin (richCount g)) :
    (lineGraph g).degree i=richDegree g i := by
  have he : (lineGraph g).neighborFinset i=richNeighbors g i := by
    ext j
    rw [SimpleGraph.mem_neighborFinset,lineGraph_adjacency]
  rw [←SimpleGraph.card_neighborFinset_eq_degree,he]
  exact (rich_rows g i).2.2.2.1

 theorem lineGraph_connected (g : PlatonicModel) : (lineGraph g).Connected := by
  letI : Nonempty (Fin (richCount g)) := ⟨richRoot g⟩
  have hr : ∀i : Fin (richCount g),(lineGraph g).Reachable i (richRoot g) := by
    intro k
    apply (measure (richDepth g)).wf.induction k
    intro i ih
    rcases (rich_rows g i).2.2.2.2 with he|h
    · subst i
      exact SimpleGraph.Reachable.refl _
    · exact ((lineGraph_adjacency g i (richParent g i)).mpr h.1).reachable.trans
        (ih (richParent g i) h.2)
  exact ⟨fun i j => (hr i).trans (hr j).symm⟩

 theorem lineGraph_edge_count (g : PlatonicModel) :
    (lineGraph g).edgeFinset.card=match g with
      | .tetrahedral => 72
      | .octahedral => 504
      | .icosahedral => 7200 := by
  have h := (lineGraph g).sum_degrees_eq_twice_card_edges
  simp only [lineGraph_degree] at h
  rw [rich_degree_sum] at h
  cases g <;> dsimp at h ⊢ <;> omega

/-- Vertices are precisely the complete rich intersections with actual complex
projective lines. The finite source index is absent from this vertex type. -/
abbrev ActualRichDomainLine (g : PlatonicModel) :=
  {S : Finset (Fin (size g)) // DomainSecant g S ∧ 3≤S.card}

 def actualLineGraph (g : PlatonicModel) : SimpleGraph (ActualRichDomainLine g) where
  Adj S T := S≠T ∧ (S.val∩T.val).Nonempty
  symm := ⟨fun S T h => ⟨Ne.symm h.1,by simpa only [Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

 def richLineEquiv (g : PlatonicModel) : Fin (richCount g) ≃ ActualRichDomainLine g :=
  Equiv.ofBijective (fun i => ⟨richSet g i,richSet_semantics g i⟩)
    ⟨fun i j h => richSet_injective g (congrArg Subtype.val h),fun S => by
      obtain ⟨i,hi⟩ := richSet_complete g S S.property.1 S.property.2
      exact ⟨i,Subtype.ext hi⟩⟩

 def lineGraphIso (g : PlatonicModel) : lineGraph g ≃g actualLineGraph g where
  toEquiv := richLineEquiv g
  map_rel_iff' := by
    intro i j
    change (richLineEquiv g i≠richLineEquiv g j ∧ _ ) ↔ _
    rw [ne_eq,(richLineEquiv g).injective.eq_iff]
    rfl

 theorem actualLineGraph_connected (g : PlatonicModel) : (actualLineGraph g).Connected :=
  (lineGraph_connected g).map (lineGraphIso g).toHom (lineGraphIso g).surjective

 theorem actualLineGraph_edge_count (g : PlatonicModel) :
    (actualLineGraph g).edgeSet.ncard=match g with
      | .tetrahedral => 72
      | .octahedral => 504
      | .icosahedral => 7200 := by
  classical
  letI : Fintype (ActualRichDomainLine g) := Fintype.ofEquiv _ (richLineEquiv g)
  rw [←SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
  rw [←(lineGraphIso g).card_edgeFinset_eq]
  exact lineGraph_edge_count g

end
end Holant.Certificates.PlatonicAtlas
