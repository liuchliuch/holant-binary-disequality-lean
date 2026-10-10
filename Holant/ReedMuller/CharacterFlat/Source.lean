import Holant.ReedMuller.CharacterFlat.Converse
import Holant.ReedMuller.CharacterFlat.Matching
import Holant.ReedMuller.CharacterFlat.Attachments
import Holant.ReedMuller.CharacterFlat.Factors

/-! Source Lemma 7.20, all four clauses. The public forward and converse
network theorems are imported from Bell and Converse. This file supplies the
arity-free low-arity statement; all closure operations are literal finite
sums, actual disjoint tensors, and proved nonzero factor decompositions. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem nonzeroFlat_arity_even {n : ℕ} (f : Signature ℂ n) (hf : NonzeroFlat f) : Even n := by
  obtain ⟨c,a,D,ell,hD,he⟩ := hf
  exact selfDual_arity_even D hD

/-- Every nonzero character-flat tensor of arity at most six has an actual
perfect matching, ordered Bell factors and a recorded nonzero scalar. -/
theorem source_low_arity_character_matching {n : ℕ} (hn : n≤6)
    (f : Signature ℂ n) (hf : CFlat f) (hfn : f≠0) :
    ∃ r : ℕ,r≤3 ∧ ∃ (M : Matching r n) (c : ℂˣ) (a : BinaryVector n) (ell : Character n),
      (bellDecomposition M c a ell).value=f := by
  have hnf : NonzeroFlat f := hf.resolve_left hfn
  obtain ⟨r,hr⟩ := nonzeroFlat_arity_even f hnf
  rw [←two_mul] at hr
  subst n
  have hr3 : r≤3 := by omega
  obtain ⟨M,c,a,ell,h⟩ := low_arity_character_matching r hr3 f hnf
  exact ⟨r,hr3,M,c,a,ell,h⟩

end
end Holant.ReedMuller.CharacterFlat
