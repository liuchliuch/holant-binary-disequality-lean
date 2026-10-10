import Holant.ReedMuller.SupportReconstruction.Dimension
import Holant.ReedMuller.SupportReconstruction.SliceExact
import Holant.Dihedral.SupportIntegration.Steiner
import Holant.ReedMuller.Steiner.Source

/-! The actual local card-derived slices supply every hypothesis of the
existing self-dual Steiner reconstruction theorem. -/
noncomputable section
namespace Holant.ReedMuller.SupportReconstruction
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.ZeroCardGraph
open Holant.ReedMuller.FlatNetwork Holant.ReedMuller.MatchingConsistency Holant.ReedMuller.WeightTwoIntegration
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem actual_local_slices (f : Signature ℂ n) (H : Consistent f) (hw : WeightedDeck f)
    (h0 : f (fun _=>false)=1) (hW : weightGraph f=⊥) :
    LocalSlices {x : BinaryVector n | f (wordVector x)≠0} := by
  intro i j hij
  obtain ⟨D⟩ := actual_matching_cards (by norm_num : (2:ℂ)≠0) f H hw h0 hW i j hij
  exact ⟨D.plus.edges,D.plus.ports,D.slice_exact hW⟩

 theorem support_card_eq_weight (x : BinaryVector n) : (Steiner.support x).card=binaryWeight x := by
   unfold Steiner.support binaryWeight
   congr 1
   ext i
   simp only [Finset.mem_filter,Finset.mem_univ,true_and]
   exact (by decide : ∀a : ZMod 2,a≠0 ↔ a=1) (x i)

 namespace LocalSlices
 variable {S : Set (BinaryVector n)} (A : LocalSlices S)
 include A

 theorem no_weight_two (hn : 6≤n) (x : BinaryVector n) (hx : x∈A.globalCode hn) :
     (Steiner.support x).card≠2 := by
   rw [support_card_eq_weight]
   intro he
   have hh := A.weight_dvd_four hn x hx
   rw [he] at hh
   norm_num at hh

 theorem steiner (hn : 6≤n) : Steiner.WordSteinerProperty (A.globalCode hn) :=
   (Steiner.word_steiner_iff _).mpr
     (Holant.Dihedral.SupportIntegration.steiner_of_exact_projections (A.globalCode hn)
       (A.exactMatchingProjections hn) (A.no_weight_two hn))

 theorem reedMuller (hn : 6≤n) : n=8 ∧ ∃e : CoefficientAtlas.Point ≃ Fin n,
     ∀x : BinaryVector n,x∈S ↔ (fun p=>x (e p))∈CoefficientAtlas.code := by
   have hh := Steiner.source_self_dual_steiner_reconstruction (A.globalCode hn)
     (by omega) (A.selfDual hn) (A.no_weight_two hn) (A.steiner hn)
   exact hh

 end LocalSlices
end Holant.ReedMuller.SupportReconstruction
