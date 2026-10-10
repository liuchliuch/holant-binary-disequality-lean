import Holant.Proofs.BinaryInterpolation.SingularExtraction.UnionMachine
import Holant.Proofs.BinaryInterpolation.SingularExtraction.GroupingMachine
import Holant.Proofs.BinaryInterpolation.SingularExtraction.GroupedQuery


noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Preparation
open Holant Holant.Complexity Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution FixedGadgetSubstitution.Compiler
open Holant.Complexity.UniversalPairReduction.Surgery
open RawClosedNetwork ResidueAnchors RawGrouping
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {s b : ℕ} {arity : ℕ → ℕ}
variable (F : Choice.Table K) (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l)

def classEnum : (Fin k × Fin l) ≃ Fin (k*l) :=
  Fintype.equivFinOfCardEq (by simp)

def branch (ρ : Fin k × Fin l) (r : ResidueAnchors.Input s b arity) : ResidueAnchors.Input s b arity :=
  if Live (s:=s) (b:=b) (arity:=arity) F a c k l hk hl ρ then
    UnionMachine.value s b arity (anchor F a c k l hk hl ρ) r else empty

def branchComputes (ρ : Fin k × Fin l) :
    Computes (validatedEncoding s b arity) (validatedEncoding s b arity) (branch F a c k l hk hl ρ) :=
  if h : Live (s:=s) (b:=b) (arity:=arity) F a c k l hk hl ρ then by
    refine congrComputes (UnionMachine.computes s b arity (anchor F a c k l hk hl ρ)) ?_
    intro r
    simp only [branch, if_pos h]
  else by
    refine congrComputes (constantComputes (validatedEncoding s b arity) (validatedEncoding s b arity) empty) ?_
    intro r
    simp only [branch, if_neg h]

def balanced (r : ResidueAnchors.Input s b arity) : ResidueAnchors.Input s b arity :=
  branch F a c k l hk hl (residue a c k l hk hl r) r

theorem balanced_live (r : ResidueAnchors.Input s b arity)
    (h : Live (s:=s) (b:=b) (arity:=arity) F a c k l hk hl (residue a c k l hk hl r)) :
    balanced F a c k l hk hl r = augmented F a c k l hk hl r := by
  simp only [balanced, branch, if_pos h]
  rfl

theorem balanced_dead (r : ResidueAnchors.Input s b arity)
    (h : ¬ Live (s:=s) (b:=b) (arity:=arity) F a c k l hk hl (residue a c k l hk hl r)) :
    balanced F a c k l hk hl r = empty := by simp [balanced, branch, h]

def balancedComputes : Computes (validatedEncoding s b arity) (validatedEncoding s b arity)
    (balanced F a c k l hk hl) := by
  let index : Computes (validatedEncoding s b arity) UnaryBinary.unaryEncoding
      (fun r => (classEnum k l (residue a c k l hk hl r)).val) :=
    (ResidueMachine.graphResiduesComputes k hk a c l hl
      (ResidueMachine.finEncoding k) (ResidueMachine.finEncoding l)).andThen
        (FiniteRecode.computes (ResidueMachine.residueEncoding k l) UnaryBinary.unaryEncoding
          (fun ρ => (classEnum k l ρ).val) (2*k+1+l) (ResidueMachine.residueEncoding_length k l))
  exact congrComputes (chooseComputes (validatedEncoding s b arity) (validatedEncoding s b arity) (k*l)
    (fun r => classEnum k l (residue a c k l hk hl r))
    (fun r i => branch F a c k l hk hl ((classEnum k l).symm i) r) index
    (fun i => branchComputes F a c k l hk hl ((classEnum k l).symm i)))
    (fun r => by simp [balanced])

theorem balanced_counts (r : ResidueAnchors.Input s b arity) :
    k ∣ occurrences a (balanced F a c k l hk hl r).val ∧
    l ∣ occurrences c (balanced F a c k l hk hl r).val := by
  by_cases h : Live (s:=s) (b:=b) (arity:=arity) F a c k l hk hl (residue a c k l hk hl r)
  · rw [balanced_live F a c k l hk hl r h]
    exact augmented_counts F a c k l hk hl r h
  · rw [balanced_dead F a c k l hk hl r h]
    simp [ResidueAnchors.empty, FixedGadgetSubstitution.occurrences]

variable (hab : a ≠ c) (has : a < s) (hcs : c < s)
variable (ha : arity a = 1) (hc : arity c = 1)

def first (r : ResidueAnchors.Input s b arity) :
    ResidueAnchors.Input s b (changedArity arity a k) :=
  let t := balanced F a c k l hk hl r
  ⟨groupOne a k t.val, groupOne_wellFormed a k has t.val t.property
    (GroupedQuery.selected_dvd_of_occurrences a k t ha (balanced_counts F a c k l hk hl r).1)⟩

def firstComputes : Computes (validatedEncoding s b arity)
    (validatedEncoding s b (changedArity arity a k)) (first F a c k l hk hl has ha) :=
  recode ((balancedComputes F a c k l hk hl).andThen
    (GroupingMachine.computes s b arity a k hk ha)) id (fun _ => rfl) (fun _ => rfl)

include hab hc in
theorem second_divides (r : ResidueAnchors.Input s b arity) :
    l ∣ (selected c (first F a c k l hk hl has ha r).val.vertices).length := by
  dsimp only [first]
  rw [selected_groupOne_other a c k hab]
  exact GroupedQuery.selected_dvd_of_occurrences c l (balanced F a c k l hk hl r) hc
    (balanced_counts F a c k l hk hl r).2

def grouped (r : ResidueAnchors.Input s b arity) :
    ResidueAnchors.Input s b (changedArity (changedArity arity a k) c l) :=
  let t := first F a c k l hk hl has ha r
  ⟨groupOne c l t.val, groupOne_wellFormed c l hcs t.val t.property
    (second_divides F a c k l hk hl hab has ha hc r)⟩

/-- End-to-end actual preprocessing from original bytes through both grouping
passes. Every parser, selector, count, range and endpoint copy is compiled. -/
def computes : Computes (validatedEncoding s b arity)
    (validatedEncoding s b (changedArity (changedArity arity a k) c l))
    (grouped F a c k l hk hl hab has hcs ha hc) :=
  recode ((firstComputes F a c k l hk hl has ha).andThen
    (GroupingMachine.computes s b (changedArity arity a k) c l hl
      (by simp [changedArity, Ne.symm hab, hc]))) id (fun _ => rfl) (fun _ => rfl)

theorem grouped_live (r : ResidueAnchors.Input s b arity)
    (h : Live (s:=s) (b:=b) (arity:=arity) F a c k l hk hl (residue a c k l hk hl r)) :
    (grouped F a c k l hk hl hab has hcs ha hc r).val =
      groupTwo a c k l (augmented F a c k l hk hl r).val := by
  simp only [grouped, first, balanced_live F a c k l hk hl r h, groupTwo]

theorem grouped_dead (r : ResidueAnchors.Input s b arity)
    (h : ¬ Live (s:=s) (b:=b) (arity:=arity) F a c k l hk hl (residue a c k l hk hl r)) :
    (grouped F a c k l hk hl hab has hcs ha hc r).val = ⟨[],[]⟩ := by
  simp [grouped, first, balanced_dead F a c k l hk hl r h, ResidueAnchors.empty,
    groupOne, keep, selected, blocks]

theorem primitive_bound (r : ResidueAnchors.Input s b arity) :
    primitiveCost (computes (s:=s) (b:=b) (arity:=arity) F a c k l hk hl hab has hcs ha hc).machine
      ((computes (s:=s) (b:=b) (arity:=arity) F a c k l hk hl hab has hcs ha hc).outputs r).steps
      (some (Turing.initList (computes (s:=s) (b:=b) (arity:=arity) F a c k l hk hl hab has hcs ha hc).machine.computer
        ((validatedEncoding s b arity).encode r))) ≤
      (primitivePolynomial (computes (s:=s) (b:=b) (arity:=arity) F a c k l hk hl hab has hcs ha hc)).eval
        ((validatedEncoding s b arity).encode r).length :=
  computes_primitive_cost (computes (s:=s) (b:=b) (arity:=arity) F a c k l hk hl hab has hcs ha hc) r

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Preparation
