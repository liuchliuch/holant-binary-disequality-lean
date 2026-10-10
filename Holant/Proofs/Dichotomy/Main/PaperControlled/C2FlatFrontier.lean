import Holant.Proofs.Dichotomy.Main.PaperControlled.C2OrdinaryPairOutcome
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2FlatFamily
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2FlatRestart
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2BinaryFlat
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2PrimeCurrent

/-! An honest whole-current frontier. Flat retained families are tractable;
otherwise an actual retained nonflat prime minimum is odd, is quaternary, or
has a genuine smaller actual output and a fully implemented restart. The
quaternary base produces Eq4 without a supplied matching-deck hypothesis.
An odd retained minimum remains an explicit source obligation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2FlatFrontier
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
namespace F
export GlobalCloseCompletionRetainedFlatLeaf (Predicate exists_minimum)
end F
namespace R
export GlobalCloseCompletionRetainedPredicateLeaf (Minimum)
end R
namespace S
export GlobalCloseCompletionC2FlatRestart (Output produce)
end S
namespace O
export GlobalCloseCompletionStopOrdinarySource (family table)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (torsion : ResidualTorsion P.family) (hI : RetainsIdentity P.family)
variable (cardTwo : Nat.card (completeGroup P.family torsion)=2)
variable (M : R.Minimum G P (F.Predicate G))

include torsion hI cardTwo in
theorem quaternary (f : Signature (OI.K G) 4) (literal : M.signature=⟨4,f⟩) :
    PaperControlled.C2OrdinaryPairOutcome.HasEq4 (O.table G P) ∨
      Tract (O.family G P) ∨ PaperControlledHardness.Original G ∨ Nonempty (S.Output G P M) := by
  classical
  by_cases lower : ∀q : Signature (OI.K G) 2,Gadget.Realizes P.family .disequality q→F.Predicate G ⟨2,q⟩
  · have retained : (⟨4,f⟩ : AnySignature (OI.K G))∈P.family := literal ▸ M.retained
    have prime : Prime (⟨4,f⟩ : AnySignature (OI.K G)) := literal ▸ M.prime
    have actual := Gadget.realizes_of_mem P.family .disequality f retained
    have stable : ∀g∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g := by
      intro g member
      rcases member with rfl|⟨key,rfl⟩
      · exact Or.inl rfl
      · exact GlobalCloseCompletionC2FlatMatching.matching P.family torsion hI
          (ClosurePhysicalBridge.complexEmbedding G) _ (by norm_num)
          (lower _ (rawCard_realizes_exact P.family torsion hI (by norm_num) f actual key))
    rcases PaperControlled.C2PrimeCurrent.classified G P torsion hI cardTwo f retained prime stable with anchor|tract|hard
    · exact Or.inl anchor
    · exact Or.inr (Or.inl tract)
    · exact Or.inr (Or.inr (Or.inl hard))
  · push Not at lower
    obtain ⟨q,actual,bad⟩ := lower
    have nonzero := GlobalCloseCompletionC2FlatNonzero.nonzero (ClosurePhysicalBridge.complexEmbedding G) q bad
    refine Or.inr (Or.inr (Or.inr ⟨⟨⟨2,q⟩,nonzero,by norm_num,actual,bad,?_⟩⟩))
    simp only [literal]
    norm_num

variable (c : OI.K G) (hc : c≠0)
variable (actualRM : Gadget.Realizes P.family .disequality (c • GlobalCloseCompletionC2RMActual.rm))

include torsion hI cardTwo hc actualRM in
theorem minimum_cases : Odd M.signature.1 ∨ M.signature.1=4 ∨ Nonempty (S.Output G P M) := by
  classical
  generalize literal : M.signature=q
  obtain ⟨n,f⟩ := q
  have bad : ¬F.Predicate G ⟨n,f⟩ := literal ▸ M.bad
  have positive := GlobalCloseCompletionC2FlatNonzero.positive (ClosurePhysicalBridge.complexEmbedding G) f bad
  rcases Nat.even_or_odd n with even|odd
  · by_cases four : n=4
    · exact Or.inr (Or.inl four)
    have two : n≠2 := by
      intro hn
      subst n
      apply bad
      right
      exact GlobalCloseCompletionC2BinaryFlat.retained P.family torsion hI cardTwo
        (ClosurePhysicalBridge.complexEmbedding G) f (literal ▸ M.retained) (literal ▸ M.prime)
    have six : 6≤n := by obtain ⟨k,hk⟩ := even;omega
    obtain ⟨m,rfl⟩ : ∃m,n=m+2 := ⟨n-2,by omega⟩
    exact Or.inr (Or.inr (S.produce G P M torsion hI cardTwo c hc actualRM f literal six even))
  · exact Or.inl odd

include torsion hI cardTwo hc actualRM in
theorem frontier : Tract (O.family G P) ∨ PaperControlledHardness.Original G ∨
    PaperControlled.C2OrdinaryPairOutcome.HasEq4 (O.table G P) ∨
    ∃M : R.Minimum G P (F.Predicate G),Odd M.signature.1 ∨ Nonempty (S.Output G P M) := by
  classical
  by_cases flat : ∀f∈P.family,F.Predicate G f
  · exact Or.inl (GlobalCloseCompletionC2FlatFamily.tract G P flat)
  have bad : ∃i : Fin P.count,¬F.Predicate G ⟨P.arity i.val,P.table i⟩ := by
    by_contra! all
    exact flat (by rintro f ⟨i,rfl⟩;exact all i)
  obtain ⟨M⟩ := F.exists_minimum G P bad
  rcases minimum_cases G P torsion hI cardTwo M c hc actualRM with odd|four|decrease
  · exact Or.inr (Or.inr (Or.inr ⟨M,Or.inl odd⟩))
  · generalize literal : M.signature=q at four
    obtain ⟨n,f⟩ := q
    dsimp at four
    subst n
    rcases quaternary G P torsion hI cardTwo M f literal with anchor|tract|hard|decrease
    · exact Or.inr (Or.inr (Or.inl anchor))
    · exact Or.inl tract
    · exact Or.inr (Or.inl hard)
    · exact Or.inr (Or.inr (Or.inr ⟨M,Or.inr decrease⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨M,Or.inr decrease⟩))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2FlatFrontier
end
