import Holant.Complexity.FixedGadgetSubstitution.Compiler.Compile
import Holant.Complexity.FixedGadgetSubstitution.Partition
import Holant.Complexity.OracleOneQuery.ContextReduction
import Holant.Complexity.FixedFieldMachines.ScalarPower.Correction

/-! A genuine encoded oracle reduction for fixed ordinary gadget substitution.
The fixed local denotation identities are the mathematical gadget hypotheses.
Replacement compilation, occurrence counting, oracle calling and scalar-power
correction are all implemented by proved finite Boolean-stack programs. -/
namespace Holant.Complexity.FixedGadgetSubstitution
open Computability BinaryCompose FixedFieldMachines Holant.Algebraic
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
variable {K : Type} [Field K] [Algebra ℚ K] {n sourceCount s b : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K n) (templates : ℕ → Template)
variable (hg : ∀label < sourceCount,(templates label).WellFormed s b arity)
variable (T : ExactSignatureTables n s b arity)
variable (source : (i : Fin sourceCount) → Signature (Fin n → ℚ) (sourceArity templates i.val))

def sourceTables : ExactSignatureTables n sourceCount b (sourceArity templates) where
  vertex := source
  edge := T.edge

def compilerHypotheses : ∀label < sourceCount,
    (templates label).WellFormed s b arity ∧
      (templates label).boundary=sourceArity templates label :=
  fun label h => ⟨hg label h,rfl⟩

/-- The same fixed original coefficient field and faithful answer codec are used
on both sides; the source table only replaces its fixed vertex signatures. -/
def reduction (label : ℕ) (scale : K) (hscale : scale≠0)
    (hdenote : ∀i : Fin sourceCount,
      ((templates i.val).network (hg i.val i.isLt)
        (fun j x => F.decode (T.vertex j x))
        (fun j x y => F.decode (T.edge j x y))).denote =
          (if i.val=label then scale else 1) • (fun x => F.decode (source i x))) :
    PolyTimeOracleReduction
      (RawClosedNetwork.validatedEncoding sourceCount b (sourceArity templates)) F.encoding
      (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      ((sourceTables templates T source).evaluate F) (T.evaluate F) := by
  let a := Compiler.withOccurrencesComputes sourceCount b (sourceArity templates)
    templates s arity (compilerHypotheses templates hg) label
  let correction := ScalarPower.correction F scale
  apply OracleOneQuery.Context.of_eq a correction (T.outputBound F)
    ((sourceTables templates T source).evaluate F)
  intro r
  have hp := replacement_scale_power templates r.val r.property hg
    (fun i x => F.decode (source i x)) (fun j x => F.decode (T.vertex j x))
    (fun j x y => F.decode (T.edge j x y)) label scale hdenote
  change T.evaluate F (Compiler.value sourceCount b (sourceArity templates) templates s arity
      (compilerHypotheses templates hg) r) =
    scale^occurrences label r.val * (sourceTables templates T source).evaluate F r at hp
  change (sourceTables templates T source).evaluate F r =
    T.evaluate F (Compiler.value sourceCount b (sourceArity templates) templates s arity
      (compilerHypotheses templates hg) r) * (scale⁻¹)^occurrences label r.val
  rw [hp,ScalarPower.cancel_scale_power scale _ hscale]

theorem reducible (label : ℕ) (scale : K) (hscale : scale≠0)
    (hdenote : ∀i : Fin sourceCount,
      ((templates i.val).network (hg i.val i.isLt)
        (fun j x => F.decode (T.vertex j x))
        (fun j x y => F.decode (T.edge j x y))).denote =
          (if i.val=label then scale else 1) • (fun x => F.decode (source i x))) :
    OracleReducible
      (RawClosedNetwork.validatedEncoding sourceCount b (sourceArity templates)) F.encoding
      (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      ((sourceTables templates T source).evaluate F) (T.evaluate F) :=
  ⟨reduction F templates hg T source label scale hscale hdenote⟩

end
end Holant.Complexity.FixedGadgetSubstitution
