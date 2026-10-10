import Holant.Certificates.PlatonicIncidence.GraphTetrahedral
import Holant.Certificates.PlatonicIncidence.GraphOctahedral
import Holant.Certificates.PlatonicIncidence.GraphIcosahedral
import Holant.Certificates.PlatonicIncidence.Subspaces
import Holant.Certificates.PlatonicIncidence.GraphConnectivity

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem neighbor_certificate (g : PlatonicModel) :
    (∀i : Fin (size g),i∉neighbors g i) ∧
    (∀i j : Fin (size g),j∈neighbors g i ↔ i∈neighbors g j) ∧
    (∀i : Fin (size g),(neighbors g i).card=degree g) := by
  cases g
  · exact tetrahedral_neighbor_certificate
  · exact octahedral_neighbor_certificate
  · exact icosahedral_neighbor_certificate

theorem pair_certificate (g : PlatonicModel) (i j : Fin (size g)) (hij : i≠j) :
    i∈globalLine g (pairLine g i j) ∧ j∈globalLine g (pairLine g i j) ∧
    (j∈neighbors g i ↔ 3≤(globalLine g (pairLine g i j)).card) := by
  cases g
  · fin_cases i
    · exact tetrahedral_pair_0 j hij
    · exact tetrahedral_pair_1 j hij
    · exact tetrahedral_pair_2 j hij
    · exact tetrahedral_pair_3 j hij
    · exact tetrahedral_pair_4 j hij
    · exact tetrahedral_pair_5 j hij
    · exact tetrahedral_pair_6 j hij
    · exact tetrahedral_pair_7 j hij
    · exact tetrahedral_pair_8 j hij
    · exact tetrahedral_pair_9 j hij
    · exact tetrahedral_pair_10 j hij
    · exact tetrahedral_pair_11 j hij
  · fin_cases i
    · exact octahedral_pair_0 j hij
    · exact octahedral_pair_1 j hij
    · exact octahedral_pair_2 j hij
    · exact octahedral_pair_3 j hij
    · exact octahedral_pair_4 j hij
    · exact octahedral_pair_5 j hij
    · exact octahedral_pair_6 j hij
    · exact octahedral_pair_7 j hij
    · exact octahedral_pair_8 j hij
    · exact octahedral_pair_9 j hij
    · exact octahedral_pair_10 j hij
    · exact octahedral_pair_11 j hij
    · exact octahedral_pair_12 j hij
    · exact octahedral_pair_13 j hij
    · exact octahedral_pair_14 j hij
    · exact octahedral_pair_15 j hij
    · exact octahedral_pair_16 j hij
    · exact octahedral_pair_17 j hij
    · exact octahedral_pair_18 j hij
    · exact octahedral_pair_19 j hij
    · exact octahedral_pair_20 j hij
    · exact octahedral_pair_21 j hij
    · exact octahedral_pair_22 j hij
    · exact octahedral_pair_23 j hij
  · fin_cases i
    · exact icosahedral_pair_0 j hij
    · exact icosahedral_pair_1 j hij
    · exact icosahedral_pair_2 j hij
    · exact icosahedral_pair_3 j hij
    · exact icosahedral_pair_4 j hij
    · exact icosahedral_pair_5 j hij
    · exact icosahedral_pair_6 j hij
    · exact icosahedral_pair_7 j hij
    · exact icosahedral_pair_8 j hij
    · exact icosahedral_pair_9 j hij
    · exact icosahedral_pair_10 j hij
    · exact icosahedral_pair_11 j hij
    · exact icosahedral_pair_12 j hij
    · exact icosahedral_pair_13 j hij
    · exact icosahedral_pair_14 j hij
    · exact icosahedral_pair_15 j hij
    · exact icosahedral_pair_16 j hij
    · exact icosahedral_pair_17 j hij
    · exact icosahedral_pair_18 j hij
    · exact icosahedral_pair_19 j hij
    · exact icosahedral_pair_20 j hij
    · exact icosahedral_pair_21 j hij
    · exact icosahedral_pair_22 j hij
    · exact icosahedral_pair_23 j hij
    · exact icosahedral_pair_24 j hij
    · exact icosahedral_pair_25 j hij
    · exact icosahedral_pair_26 j hij
    · exact icosahedral_pair_27 j hij
    · exact icosahedral_pair_28 j hij
    · exact icosahedral_pair_29 j hij
    · exact icosahedral_pair_30 j hij
    · exact icosahedral_pair_31 j hij
    · exact icosahedral_pair_32 j hij
    · exact icosahedral_pair_33 j hij
    · exact icosahedral_pair_34 j hij
    · exact icosahedral_pair_35 j hij
    · exact icosahedral_pair_36 j hij
    · exact icosahedral_pair_37 j hij
    · exact icosahedral_pair_38 j hij
    · exact icosahedral_pair_39 j hij
    · exact icosahedral_pair_40 j hij
    · exact icosahedral_pair_41 j hij
    · exact icosahedral_pair_42 j hij
    · exact icosahedral_pair_43 j hij
    · exact icosahedral_pair_44 j hij
    · exact icosahedral_pair_45 j hij
    · exact icosahedral_pair_46 j hij
    · exact icosahedral_pair_47 j hij
    · exact icosahedral_pair_48 j hij
    · exact icosahedral_pair_49 j hij
    · exact icosahedral_pair_50 j hij
    · exact icosahedral_pair_51 j hij
    · exact icosahedral_pair_52 j hij
    · exact icosahedral_pair_53 j hij
    · exact icosahedral_pair_54 j hij
    · exact icosahedral_pair_55 j hij
    · exact icosahedral_pair_56 j hij
    · exact icosahedral_pair_57 j hij
    · exact icosahedral_pair_58 j hij
    · exact icosahedral_pair_59 j hij

theorem line_pair_certificate (g : PlatonicModel) (t : Fin (secantCount g))
    (i j : Fin (size g)) (hi : i∈globalLine g t) (hj : j∈globalLine g t) :
    i=j ∨ pairLine g i j=t := by
  cases g
  · exact tetrahedral_all_pairs t i hi j hj
  · exact octahedral_all_pairs t i hi j hj
  · exact icosahedral_all_pairs t i hi j hj

def domainGraph (g : PlatonicModel) : SimpleGraph (Fin (size g)) where
  Adj i j := j∈neighbors g i
  symm := ⟨fun i j h => (neighbor_certificate g).2.1 i j |>.mp h⟩
  loopless := ⟨fun i => (neighbor_certificate g).1 i⟩

instance (g : PlatonicModel) : DecidableRel (domainGraph g).Adj :=
  fun i j => inferInstanceAs (Decidable (j∈neighbors g i))

theorem domainGraph_degree (g : PlatonicModel) (i : Fin (size g)) :
    ((domainGraph g).neighborFinset i).card=degree g := by
  have he : (domainGraph g).neighborFinset i=neighbors g i := by
    ext j
    exact SimpleGraph.mem_neighborFinset (domainGraph g) i j
  rw [he]
  exact (neighbor_certificate g).2.2 i

/-- The graph adjacency test is exactly sharing an actual rich projective
secant. All finite-table indices are eliminated from this public statement. -/
theorem domainGraph_semantics (g : PlatonicModel) (i j : Fin (size g)) :
    (domainGraph g).Adj i j ↔ i≠j ∧ ∃S : Finset (Fin (size g)),
      DomainSecant g S ∧ 3≤S.card ∧ i∈S ∧ j∈S := by
  constructor
  · intro h
    have hij : i≠j := fun he => (neighbor_certificate g).1 i (he ▸ h)
    have hp := pair_certificate g i j hij
    exact ⟨hij,globalLine g (pairLine g i j),globalLine_semantics g _,hp.2.2.mp h,hp.1,hp.2.1⟩
  · rintro ⟨hij,S,hS,hcard,hi,hj⟩
    obtain ⟨t,_,rfl⟩ := Finset.mem_map.mp ((domainLines_exact g S).mpr hS)
    have ht := (line_pair_certificate g t i j hi hj).resolve_left hij
    apply (pair_certificate g i j hij).2.2.mpr
    rwa [ht]

/-- Every dimension≤2 complex kernel deletion is connected and nonempty.
The proof uniformly covers empty, singleton, ordinary two-point, and every
rich-line intersection. -/
theorem kernel_deleted_connected (g : PlatonicModel) (W : Submodule ℂ Mat)
    (hW : Module.finrank ℂ W≤2) :
    ((domainGraph g).induce {i | representative g i∉W}).Connected := by
  classical
  have hdeg (i : Fin (size g)) : degree g≤((domainGraph g).neighborFinset i).card := by
    rw [domainGraph_degree]
  have hlarge : Fintype.card (Fin (size g))+maximumLineSize g<2*degree g := by
    cases g <;> decide
  have hsize : maximumLineSize g<Fintype.card (Fin (size g)) := by
    cases g <;> decide
  have hc := connected_after_deletion (domainGraph g) (degree g) (maximumLineSize g)
    hdeg hlarge hsize (deletion g W) (deletion_bound g W hW)
  have he : {i | i∉deletion g W}={i | representative g i∉W} := by
    ext i
    simp only [Set.mem_setOf_eq,mem_deletion]
  rw [he] at hc
  exact hc

end
end Holant.Certificates.PlatonicIncidence
