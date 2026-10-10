import Holant.Proofs.Hardness.GeneralEODEQProducerNormalize
import Holant.Proofs.Hardness.GeneralEOPinnedDescentPalette
import Holant.Proofs.Hardness.GeneralEODEQProducerSupport

/-! Original-label interface for the pinned central DEQ4 producer. Its only
adjoined row is literal directed01, and every retained source label still
means the coefficient table of that same original input signature. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducer
open Holant Holant.Complexity Holant.Tractable FixedGadgetSubstitution
namespace P
export GeneralEOPinnedDescentPalette (palette arity pinLabel palette_pin corollaLabels corolla_exact)
end P
namespace C
export GeneralEODEQProducerCore (Pair)
end C
namespace N
export GeneralEODEQProducerNormalize (Produced produce)
end N
export GeneralEODEQProducerSupportBasic (Pure xorList)
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

/-- The graph begins with the original labelled corolla. Balanced fixed
coordinates are removed by paired pins; native loops and a literal two-copy
chain then give the exact nonzero scalar DEQ4 denotation. -/
theorem from_pair (j : Fin s) (he : Signature.CentralSupport (G j)) (p : C.Pair (G j)) :
    Nonempty (N.Produced (P.palette G)) := by
  have hc : Signature.CentralSupport (Network.corolla (G j)).denote := by
    simpa only [Network.denote_corolla] using he
  have hp : C.Pair (Network.corolla (G j)).denote := by
    simpa only [Network.denote_corolla] using p
  exact N.produce (P.palette G) P.pinLabel (P.palette_pin G)
    (Network.corolla (G j)) (P.corollaLabels G j) (P.corolla_exact G j)
    (fun i => Fin.elim0 i) hc hp

/-- The same original row and the same selected sign supply both hypotheses.
Pure means every odd XOR of supported words lies in that sign's weak halfspace.
The conclusion contains no externally supplied network or equality resource. -/
theorem producer (j : Fin s) (sign : Holant.Tractable.EOSign)
    (he : Signature.CentralSupport (G j))
    (hs : EONegativeWitness.Supports sign ⟨a j.val,G j⟩)
    (hp : ¬Pure sign (G j)) : Nonempty (N.Produced (P.palette G)) := by
  obtain ⟨p⟩ := GeneralEODEQProducerSupport.exists_pair sign he hs hp
  exact from_pair G j he p

/-- Expanded literal-graph conclusion over the unchanged original rows plus
one directed01 row. All coefficients, labels, native edges and the nonzero
scalar are explicit in the returned witness. -/
theorem exists_network (j : Fin s) (sign : Holant.Tractable.EOSign)
    (he : Signature.CentralSupport (G j))
    (hs : EONegativeWitness.Supports sign ⟨a j.val,G j⟩)
    (hp : ¬Pure sign (G j)) :
    ∃ Q : Network AlgebraicComplex 4,
      ∃ L : Labelling Q.shape (s+1) 1 (P.arity (s:=s) (a:=a)),
        LabelledNetwork.Exact (P.palette G) Q L ∧
        (∀e,Q.edge e=Signature.disequality) ∧
        ∃ c : AlgebraicComplex,c≠0 ∧ Q.denote=c • ExactTwoSignatures.E := by
  obtain ⟨Q⟩ := producer G j sign he hs hp
  exact ⟨Q.network,Q.labels,Q.exact,Q.native,Q.scalar,Q.nonzero,Q.denote⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducer
