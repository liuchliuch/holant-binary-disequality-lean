import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportExtraction
import Holant.Proofs.Hardness.EOBinaryPlaneClassification

/-! A ternary-XOR hole in an arbitrary original support produces an actual
three-supported binary gadget. The sixteen residual ternary support patterns
use pins, or the unique three-point projection with no possible cancellation.
All coefficients remain in the original field; no support-indicator oracle is
introduced. The selected support shift is compiled separately with literal X. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonclosedSupportExtraction
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace G
export GeneralEOPairedFamilyExtractionGadget (Gadget denote direct direct_value trace trace_value)
end G
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle (evaluate evaluate_compose)
end B
namespace I
export GeneralEOPairedFamilyExtractionInteraction (compose)
end I
namespace E
export OrdinaryNegativeAffineSupportExtraction (shift)
end E
namespace C
export GeneralEONegativeClosedSupport (Closed)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : Type*} [Field K]

def support (f : Signature K 2) : Finset (Fin 2→Bool) := by
  classical
  exact Finset.univ.filter (fun z=>f z≠0)
def Three (f : Signature K 2) : Prop := (support f).card=3

private theorem binary_univ : (Finset.univ : Finset (Fin 2→Bool))=
    {![false,false],![false,true],![true,false],![true,true]} := by decide

private theorem three_ff_ft_tt (f : Signature K 2)
    (h00 : f ![false,false]≠0) (h01 : f ![false,true]≠0)
    (h10 : f ![true,false]=0) (h11 : f ![true,true]≠0) : Three f := by
  classical
  simp [Three,support,binary_univ,Finset.filter_insert,Finset.filter_singleton,h00,h01,h10,h11]
private theorem three_ff_tf_tt (f : Signature K 2)
    (h00 : f ![false,false]≠0) (h01 : f ![false,true]=0)
    (h10 : f ![true,false]≠0) (h11 : f ![true,true]≠0) : Three f := by
  classical
  simp [Three,support,binary_univ,Finset.filter_insert,Finset.filter_singleton,h00,h01,h10,h11]
private theorem three_ff_ft_tf (f : Signature K 2)
    (h00 : f ![false,false]≠0) (h01 : f ![false,true]≠0)
    (h10 : f ![true,false]≠0) (h11 : f ![true,true]=0) : Three f := by
  classical
  simp [Three,support,binary_univ,Finset.filter_insert,Finset.filter_singleton,h00,h01,h10,h11]
private theorem three_ft_tf_tt (f : Signature K 2)
    (h00 : f ![false,false]=0) (h01 : f ![false,true]≠0)
    (h10 : f ![true,false]≠0) (h11 : f ![true,true]≠0) : Three f := by
  classical
  simp [Three,support,binary_univ,Finset.filter_insert,Finset.filter_singleton,h00,h01,h10,h11]

@[simp] theorem substitute_three {m : ℕ} (p q r : Bool ⊕ Fin m) (x : Fin m→Bool) :
    T.substitute ![p,q,r] x=![Sum.elim id x p,Sum.elim id x q,Sum.elim id x r] := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem snoc_two (a b c : Bool) : Fin.snoc (![a,b] : Fin 2→Bool) c=![a,b,c] := by
  funext i
  fin_cases i <;> rfl

/-- Every residual support pattern has a three-support pinning, except the
exact three-point row, whose projection has disjoint nonzero summands. -/
theorem ternary (f : Signature K 3)
    (h000 : f ![false,false,false]≠0)
    (h101 : f ![true,false,true]≠0)
    (h011 : f ![false,true,true]≠0)
    (h110 : f ![true,true,false]=0) :
    ∃q : G.Gadget 3 2,Three (G.denote f q) := by
  classical
  by_cases h001 : f ![false,false,true]=0 <;>
    by_cases h010 : f ![false,true,false]=0 <;>
    by_cases h100 : f ![true,false,false]=0 <;>
    by_cases h111 : f ![true,true,true]=0
  · refine ⟨G.trace (G.direct [![.inr 2,.inr 0,.inr 1]]),?_⟩
    apply three_ff_ft_tt <;>
      simp [G.trace_value,G.direct_value,B.evaluate,Fin.sum_univ_two,
        h000,h001,h010,h011,h100,h101,h110,h111]
  · refine ⟨G.direct [![.inr 0,.inr 1,.inl true]],?_⟩
    apply three_ft_tf_tt <;>
      simp [G.direct_value,B.evaluate,
        h000,h001,h010,h011,h100,h101,h110,h111]
  · refine ⟨G.direct [![.inr 0,.inl false,.inr 1]],?_⟩
    apply three_ff_tf_tt <;>
      simp [G.direct_value,B.evaluate,
        h000,h001,h010,h011,h100,h101,h110,h111]
  · refine ⟨G.direct [![.inr 0,.inl false,.inr 1]],?_⟩
    apply three_ff_tf_tt <;>
      simp [G.direct_value,B.evaluate,
        h000,h001,h010,h011,h100,h101,h110,h111]
  · refine ⟨G.direct [![.inl false,.inr 0,.inr 1]],?_⟩
    apply three_ff_tf_tt <;>
      simp [G.direct_value,B.evaluate,
        h000,h001,h010,h011,h100,h101,h110,h111]
  · refine ⟨G.direct [![.inl false,.inr 0,.inr 1]],?_⟩
    apply three_ff_tf_tt <;>
      simp [G.direct_value,B.evaluate,
        h000,h001,h010,h011,h100,h101,h110,h111]
  · refine ⟨G.direct [![.inl false,.inr 0,.inr 1]],?_⟩
    apply three_ff_tf_tt <;>
      simp [G.direct_value,B.evaluate,
        h000,h001,h010,h011,h100,h101,h110,h111]
  · refine ⟨G.direct [![.inl false,.inr 0,.inr 1]],?_⟩
    apply three_ff_tf_tt <;>
      simp [G.direct_value,B.evaluate,
        h000,h001,h010,h011,h100,h101,h110,h111]
  · refine ⟨G.direct [![.inl false,.inr 0,.inr 1]],?_⟩
    apply three_ff_ft_tt <;>
      simp [G.direct_value,B.evaluate,
        h000,h001,h010,h011,h100,h101,h110,h111]
  · refine ⟨G.direct [![.inl false,.inr 0,.inr 1]],?_⟩
    apply three_ff_ft_tt <;>
      simp [G.direct_value,B.evaluate,
        h000,h001,h010,h011,h100,h101,h110,h111]
  · refine ⟨G.direct [![.inl false,.inr 0,.inr 1]],?_⟩
    apply three_ff_ft_tt <;>
      simp [G.direct_value,B.evaluate,
        h000,h001,h010,h011,h100,h101,h110,h111]
  · refine ⟨G.direct [![.inl false,.inr 0,.inr 1]],?_⟩
    apply three_ff_ft_tt <;>
      simp [G.direct_value,B.evaluate,
        h000,h001,h010,h011,h100,h101,h110,h111]
  · refine ⟨G.direct [![.inr 0,.inl false,.inr 1]],?_⟩
    apply three_ff_ft_tt <;>
      simp [G.direct_value,B.evaluate,
        h000,h001,h010,h011,h100,h101,h110,h111]
  · refine ⟨G.direct [![.inr 0,.inl false,.inr 1]],?_⟩
    apply three_ff_ft_tt <;>
      simp [G.direct_value,B.evaluate,
        h000,h001,h010,h011,h100,h101,h110,h111]
  · refine ⟨G.direct [![.inr 0,.inr 1,.inl false]],?_⟩
    apply three_ff_ft_tf <;>
      simp [G.direct_value,B.evaluate,
        h000,h001,h010,h011,h100,h101,h110,h111]
  · refine ⟨G.direct [![.inr 0,.inr 1,.inl false]],?_⟩
    apply three_ff_ft_tf <;>
      simp [G.direct_value,B.evaluate,
        h000,h001,h010,h011,h100,h101,h110,h111]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonclosedSupportExtraction
end
