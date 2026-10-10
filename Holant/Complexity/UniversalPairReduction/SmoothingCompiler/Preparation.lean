import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Validated

/-! All three literal original-family queries and the scalar-control flags are
produced from the unchanged original one-pair input bytes. -/
namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Computability BinaryCompose FixedFieldMachines RawClosedNetwork FixedGadgetSubstitution
variable {s : ℕ} {arity : ℕ → ℕ} {S : NetworkShape 2}

abbrev Flags := Bool × Bool
abbrev flagsEncoding := pairEncoding encodingBoolBool encodingBoolBool

def flags (r : Input s arity) : Flags :=
  ((Smoothing.compile s r.val).circle,decide (FixedGadgetSubstitution.occurrences s r.val=1))

noncomputable def flagsComputes : Computes (inputEncoding s arity) flagsEncoding flags :=
  pairComputes (circleFlagComputes s arity) (hasPairComputes s arity)

abbrev targetEncoding := validatedEncoding s 1 arity
abbrev preparedEncoding := pairEncoding (targetEncoding (s:=s) (arity:=arity))
  (pairEncoding (targetEncoding (s:=s) (arity:=arity))
    (pairEncoding (targetEncoding (s:=s) (arity:=arity)) flagsEncoding))

def prepared (L : Labelling S s 1 arity) (r : Input s arity) :=
  (Surgery.query r,(OrderedQueries.plus L (forget s arity r),
    (OrderedQueries.minus L (forget s arity r),flags r)))

/-- Concrete preparation for three sequential oracle calls, in S,+,- order. -/
noncomputable def preparedComputes (L : Labelling S s 1 arity) :
    Computes (inputEncoding s arity) (preparedEncoding (s:=s) (arity:=arity)) (prepared L) :=
  pairComputes (queryComputes s arity)
    (pairComputes ((forgetComputes s arity).andThen (OrderedQueries.computes L (Equiv.refl _)))
      (pairComputes ((forgetComputes s arity).andThen (OrderedQueries.computes L (Equiv.swap 0 1)))
        flagsComputes))

end Holant.Complexity.UniversalPairReduction.SmoothingCompiler
