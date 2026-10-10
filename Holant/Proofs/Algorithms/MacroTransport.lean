import Holant.Proofs.Algorithms.ControlledReduction
import Holant.Complexity.FixedGadgetSubstitution.Adjoin


namespace Holant.LocalDrafts.MainChain.MacroTransport
open Computability Holant.Complexity Holant.Complexity.BinaryCompose
open Holant.Algebraic Holant.Complexity.FixedGadgetSubstitution
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

variable {K : Type} [Field K] [Algebra ℚ K] {n sourceCount s b : ℕ}
    {arity : ℕ → ℕ} (F : FixedField K n) (templates : ℕ → Template)
    (hg : ∀ label < sourceCount, (templates label).WellFormed s b arity)
    (T : ExactSignatureTables n s b arity)

/-- The finite graph compiler is used directly.  Its output length theorem
supplies the query bound required by subsequent actual-machine composition. -/
def controlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding sourceCount b (sourceArity templates)) F.encoding
    (RawClosedNetwork.validatedEncoding s b arity) F.encoding
    ((sourceTables templates T (templateCoordinates F templates hg T)).evaluate F)
    (T.evaluate F) := by
  apply controlledOneQueryOfEq
    (Compiler.computes sourceCount b (sourceArity templates) templates s arity
      (compilerHypotheses templates hg))
    (identityComputes F.encoding) (T.outputBound F)
    ((sourceTables templates T (templateCoordinates F templates hg T)).evaluate F)
  intro r
  have hlocal (i : Fin sourceCount) :
      ((templates i.val).network (hg i.val i.isLt)
        (fun j x => F.decode (T.vertex j x))
        (fun j x y => F.decode (T.edge j x y))).denote =
        (if i.val = 0 then (1 : K) else 1) •
          (fun x => F.decode (templateCoordinates F templates hg T i x)) := by
    simp only [ite_self, one_smul]
    funext x
    exact (decode_templateCoordinates F templates hg T i x).symm
  have hp := replacement_scale_power templates r.val r.property hg
    (fun i x => F.decode (templateCoordinates F templates hg T i x))
    (fun j x => F.decode (T.vertex j x))
    (fun j x y => F.decode (T.edge j x y)) 0 1 hlocal
  change T.evaluate F (Compiler.value sourceCount b (sourceArity templates)
      templates s arity (compilerHypotheses templates hg) r) =
    (1 : K)^occurrences 0 r.val *
      (sourceTables templates T (templateCoordinates F templates hg T)).evaluate F r at hp
  simpa only [one_pow, one_mul, id_eq] using hp.symm

/-- Literal finite adjoin, including all old labels and the exact new macro. -/
def adjoinControlled (g : Template) (h : g.WellFormed s b arity) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (s+1) b
        (sourceArity (Adjoin.templates s arity g))) F.encoding
      (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      ((sourceTables (Adjoin.templates s arity g) T (Adjoin.coordinates F T g h)).evaluate F)
      (T.evaluate F) :=
  controlled F (Adjoin.templates s arity g) (Adjoin.wellFormed g h) T

/-- A finite actual macro batch can be removed before a later verified reducer. -/
def thenReduction {α β : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    {f : α → β}
    (r : PolyTimeOracleReduction (RawClosedNetwork.validatedEncoding s b arity)
      F.encoding ea eb (T.evaluate F) f) :
    PolyTimeOracleReduction
      (RawClosedNetwork.validatedEncoding sourceCount b (sourceArity templates)) F.encoding
      ea eb ((sourceTables templates T (templateCoordinates F templates hg T)).evaluate F) f :=
  (controlled F templates hg T).compose r

end
end Holant.LocalDrafts.MainChain.MacroTransport
