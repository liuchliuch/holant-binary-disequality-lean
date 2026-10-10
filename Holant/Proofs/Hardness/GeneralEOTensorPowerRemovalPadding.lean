import Holant.Proofs.Hardness.GeneralEOTensorPowerRemovalCompiler
import Holant.Proofs.Hardness.GeneralEOTensorPowerRemovalTables
import Holant.Proofs.Hardness.GeneralEOTensorPowerRemovalWitness
import Holant.Proofs.BinaryInterpolation.SingularExtraction.UnionMachine

/-! Finite nonuniform residue preprocessing, literal disjoint padding, and
actual general-arity grouping. The only fixed input data are the signature
family and the positive exponent. Live/dead residues and nonzero closed anchors
are derived here; they are never an answer oracle or runtime search premise. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalPadding
open Holant Holant.Complexity Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open UniversalPairReduction.Surgery FixedGadgetSubstitution.Compiler
open GeneralEOTensorPowerRemovalRaw GeneralEOTensorPowerRemovalValue
namespace W
export GeneralEOTensorPowerRemovalWitness (Active chosen chosen_spec residue inactive_input_zero
  padded_count_mod correction_ne_zero)
end W
namespace C
export GeneralEOTensorPowerRemovalCompiler (countComputes computes)
end C
namespace D
export Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.RawDisjoint
  (copies union copies_wellFormed union_wellFormed occurrences_union occurrences_copies
   union_value copies_value bounded_of_wellFormed union_vertices union_edges copies_vertices copies_edges)
end D
namespace U
export Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.UnionMachine (value computes)
end U
namespace R
export Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.ResidueMachine
  (computes finEncoding finEncoding_length)
end R
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {s n : ℕ} {a : ℕ→ℕ}
variable (F : Choice.Table K) (f : List Bool→K) (k : ℕ) (hk : 0<k)

abbrev Input (s n : ℕ) (a : ℕ→ℕ) :=
  {r : RawClosedNetwork // r.WellFormed (s+1) 1 (sourceArity s n a)}
abbrev inputEncoding (s n : ℕ) (a : ℕ→ℕ) :=
  RawClosedNetwork.validatedEncoding (s+1) 1 (sourceArity s n a)

def empty : Input s n a := ⟨⟨[],[]⟩,by
  refine ⟨?_,?_,?_⟩
  · intro v; exact Fin.elim0 v
  · intro e; exact Fin.elim0 e
  · exact List.Perm.refl []⟩

def occurrences (r : Input s n a) : ℕ := count s r.val

def value (r : Input s n a) : K :=
  Choice.evaluate (sourceTable s F f) r.val.edges.length r.val.vertices

abbrev Active (rho : Fin k) := W.Active (occurrences (s:=s) (n:=n) (a:=a)) (value F f) k rho
abbrev residue (r : Input s n a) := W.residue occurrences k hk r

def anchor (rho : Fin k) : Input s n a :=
  if h : Active (s:=s) (n:=n) (a:=a) F f k rho then
    let w := W.chosen occurrences (value F f) k rho h
    ⟨D.copies w.val (k-1),D.copies_wellFormed w.property (k-1)⟩
  else empty

theorem anchor_nonzero (rho : Fin k) (h : Active (s:=s) (n:=n) (a:=a) F f k rho) :
    value F f (anchor (s:=s) (n:=n) (a:=a) F f k rho)≠0 := by
  simp only [anchor,dite_eq_left h,value]
  rw [D.copies_value _ _ (W.chosen occurrences (value F f) k rho h).property]
  exact pow_ne_zero _ (W.chosen_spec occurrences (value F f) k rho h).2

def branch (rho : Fin k) (r : Input s n a) : Input s n a :=
  if Active (s:=s) (n:=n) (a:=a) F f k rho then U.value (s+1) 1 (sourceArity s n a) (anchor (s:=s) (n:=n) (a:=a) F f k rho) r
  else empty

def balanced (r : Input s n a) : Input s n a := branch F f k (residue k hk r) r

def branchComputes (rho : Fin k) : Computes (inputEncoding s n a) (inputEncoding s n a)
    (branch F f k rho) := by
  by_cases h : Active (s:=s) (n:=n) (a:=a) F f k rho
  · exact congrComputes (U.computes (s+1) 1 (sourceArity s n a) (anchor (s:=s) (n:=n) (a:=a) F f k rho))
      (fun r=>by simp only [branch,ite_eq_left h])
  · exact congrComputes (constantComputes (inputEncoding s n a) (inputEncoding s n a) empty)
      (fun r=>by simp only [branch,ite_eq_right h])

def countComputes : Computes (inputEncoding s n a) UnaryBinary.unaryEncoding occurrences :=
  recode (C.countComputes s) Subtype.val (fun _=>rfl) (fun _=>rfl)

def residueComputes : Computes (inputEncoding s n a) (R.finEncoding k) (residue k hk) :=
  countComputes.andThen (R.computes k hk (R.finEncoding k) id)

def balancedComputes : Computes (inputEncoding s n a) (inputEncoding s n a)
    (balanced (s:=s) (n:=n) (a:=a) F f k hk) :=
  chooseComputes (inputEncoding s n a) (inputEncoding s n a) k (residue k hk)
    (fun r rho=>branch F f k rho r)
    (countComputes.andThen (R.computes k hk UnaryBinary.unaryEncoding Fin.val))
    (branchComputes F f k)

theorem count_eq_occurrences (r : RawClosedNetwork) :
    count s r=FixedGadgetSubstitution.occurrences s r := by
  unfold count selected FixedGadgetSubstitution.occurrences
  congr 2

theorem balanced_count (r : Input s n a) : count s (balanced F f k hk r).val%k=0 := by
  by_cases h : Active (s:=s) (n:=n) (a:=a) F f k (residue k hk r)
  · have hw := (W.chosen_spec occurrences (value F f) k (residue k hk r) h).1
    have hc := W.padded_count_mod occurrences k hk r
      (W.chosen occurrences (value F f) k (residue k hk r) h) hw.symm
    simpa only [balanced,branch,ite_eq_left h,U.value,anchor,dite_eq_left h,
      count_eq_occurrences,D.occurrences_union,D.occurrences_copies,occurrences] using hc
  · simp [balanced,branch,h,empty,count,selected]

def query (r : Input s n a) :
    {q : RawClosedNetwork // q.WellFormed (s+1) 1 (targetArity s n k a)} :=
  ⟨raw s k (balanced F f k hk r).val,
    wellFormed (balanced F f k hk r).property (balanced_count F f k hk r)⟩

/-- End-to-end literal raw valid query, including every finite residue branch. -/
def queryComputes : Computes (inputEncoding s n a)
    (RawClosedNetwork.validatedEncoding (s+1) 1 (targetArity s n k a))
    (query (s:=s) (n:=n) (a:=a) F f k hk) := by
  let rawRun : Computes (inputEncoding s n a) RawClosedNetwork.encoding
      (fun r=>raw s k r.val) := recode (C.computes s k hk) Subtype.val (fun _=>rfl) (fun _=>rfl)
  exact recode ((balancedComputes F f k hk).andThen rawRun) id (fun _=>rfl) (fun _=>rfl)

def coefficient (rho : Fin k) : K :=
  if Active (s:=s) (n:=n) (a:=a) F f k rho then (value F f (anchor (s:=s) (n:=n) (a:=a) F f k rho))⁻¹ else 0

theorem query_value (r : Input s n a) (h : Active (s:=s) (n:=n) (a:=a) F f k (residue k hk r)) :
    Choice.evaluate (targetTable s n k F f) (query F f k hk r).val.edges.length
      (query F f k hk r).val.vertices=value F f r*value F f (anchor (s:=s) (n:=n) (a:=a) F f k (residue k hk r)) := by
  rw [show (query F f k hk r).val=raw s k (balanced F f k hk r).val from rfl]
  rw [evaluate_eq (balanced F f k hk r).property (balanced_count F f k hk r)]
  change value F f (balanced F f k hk r)=_
  simp only [balanced,branch,ite_eq_left h,U.value,value]
  exact D.union_value _ _ _ (D.bounded_of_wellFormed _ r.property)
    (D.bounded_of_wellFormed _ (anchor (s:=s) (n:=n) (a:=a) F f k (residue k hk r)).property)

theorem recover (r : Input s n a) :
    Choice.evaluate (targetTable s n k F f) (query F f k hk r).val.edges.length
      (query F f k hk r).val.vertices*coefficient (s:=s) (n:=n) (a:=a) F f k (residue k hk r)=
      value F f r := by
  by_cases h : Active (s:=s) (n:=n) (a:=a) F f k (residue k hk r)
  · rw [query_value F f k hk r h]
    simp only [coefficient,ite_eq_left h]
    rw [mul_assoc,mul_inv_cancel₀ (anchor_nonzero F f k _ h),mul_one]
  · have hz := W.inactive_input_zero occurrences (value F f) k hk r h
    simp only [coefficient,ite_eq_right h,mul_zero,hz]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalPadding
