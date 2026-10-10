import Holant.ReedMuller.SupportReconstruction.Reconstruction
import Holant.ReedMuller.SupportReconstruction.SliceFormula
import Holant.ReedMuller.ZeroCardGraph.CanonicalDeck

/-! Full source7.10: actual weighted I/X cards with no original weight-two
coefficient reconstruct every equal-pair parity slice, then the entire
original Walsh support as the eight-port Reed--Muller evaluation code. -/
noncomputable section
namespace Holant.ReedMuller.SupportReconstruction
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.ZeroCardGraph
open Holant.ReedMuller.FlatNetwork Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.WeightTwoIntegration Holant.ReedMuller.CoefficientAtlas
open Holant.ReedMuller.RadonAccess Holant.Certificates.MatchingContractionClosure
set_option backward.isDefEq.respectTransparency false

/-- The common matching presentation carries actual unnormalized card
coefficients. The source's arbitrary edge order is the retained `plus.ports`;
the formula is valid for every such actual presentation. -/
 theorem source_equal_pair_slice {n : ℕ} (f : Signature ℂ n) (H : Consistent f)
    (hw : WeightedDeck f) (h0 : f (fun _=>false)=1) (hW : weightGraph f=⊥)
    (i j : Fin n) (hij : i≠j) :
    ∃D : MatchingCards f i j,
      D.plus.edges=n/2-1 ∧ Module.finrank (ZMod 2) (sliceCode D.plus.ports)=D.plus.edges ∧
      (∀x : BinaryVector n,(f (wordVector x)≠0 ∧ x i=x j) ↔
        ∃t : BinaryVector D.plus.edges,x=matchingWord D.plus.ports t+
          (binaryWeight t:ZMod 2) • (unitWord i+unitWord j)) ∧
      (∀x : BinaryVector n,x∈sliceCode D.plus.ports → 4∣binaryWeight x) := by
  obtain ⟨D⟩ := actual_matching_cards (by norm_num : (2:ℂ)≠0) f H hw h0 hW i j hij
  have hp := slice_port_count D.plus.ports hij
  refine ⟨D,by omega,sliceCode_finrank D.plus.ports,?_,?_⟩
  · intro x
    rw [D.slice_exact hW,mem_slice_formula D.plus.ports hij]
  · exact sliceCode_weight_dvd_four D.plus.ports hij

/-- Complete original-support reconstruction from the source's literal
canonical fixed-representative deck. The empty zero graph and common
matchings are derived by7.6–7.7, not supplied as hidden support premises. -/
 theorem source_reed_muller_support {n : ℕ} {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀T∈G,∃α β : ℂ,T=fun a b=>α*Signature.equality a b+β*Signature.disequality a b)
    (R : FixedIXRepresentatives) (q : Signature ℂ (n+2)) (hq : q≠0) (hn : 6≤n+2)
    (h0 : walsh q (fun _=>false)=1) (hdeck : CanonicalMatchingDeck G R q)
    (hW : weightGraph (walsh q)=⊥) :
    (∀i j : Fin (n+2),i≠j → ∃D : MatchingCards (walsh q) i j,
      D.plus.edges=(n+2)/2-1 ∧ Module.finrank (ZMod 2) (sliceCode D.plus.ports)=D.plus.edges ∧
      (∀x : BinaryVector (n+2),(walsh q (wordVector x)≠0 ∧ x i=x j) ↔
        ∃t : BinaryVector D.plus.edges,x=matchingWord D.plus.ports t+
          (binaryWeight t:ZMod 2) • (unitWord i+unitWord j)) ∧
      (∀x : BinaryVector (n+2),x∈sliceCode D.plus.ports → 4∣binaryWeight x)) ∧
    (∃D : BinaryCode (n+2),(∀x,x∈D ↔ walsh q (wordVector x)≠0) ∧ SelfDual D ∧
      2*Module.finrank (ZMod 2) D=n+2 ∧ (∀x,x∈D → 4∣binaryWeight x)) ∧
    (n+2=8 ∧ ∃e : CoefficientAtlas.Point ≃ Fin (n+2),∀x : BinaryVector (n+2),
      walsh q (wordVector x)≠0 ↔ (fun p=>x (e p))∈CoefficientAtlas.code) := by
  have ha := actualMatchingDeck_of_canonical R q hdeck
  have H := source_matching_consistency hG hspan R q hq hn hdeck
  have hw := actual_weighted_deck hG hspan R q ha
  have A := actual_local_slices (walsh q) H hw h0 hW
  refine ⟨source_equal_pair_slice (walsh q) H hw h0 hW,?_,A.reedMuller hn⟩
  exact ⟨A.globalCode hn,(fun _=>Iff.rfl),A.selfDual hn,A.half_dimension hn,A.weight_dvd_four hn⟩

end Holant.ReedMuller.SupportReconstruction
