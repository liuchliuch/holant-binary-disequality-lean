import Holant.Proofs.Dichotomy.WithoutIdentity.NoIQuaternaryReduction
import Holant.Proofs.Dichotomy.WithoutIdentity.NoISparseComplementComplete

/-! Every original endpoint quaternary now reduces to a proved conclusion
or the single whole-family pure Eq4 obligation, with its physical source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIQuaternaryPureReduction
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.EightVertex.ProductAnchor
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false

theorem pure_complement {K : Type} [Field K] (phi : K→+*AlgebraicComplex)
    (q : Signature K 4) (pure : PureEquality (RingHomRealization.mapSignature phi q)) :
    PaperTerminalBridgeComplementSign.Complement q := by
  obtain ⟨a,b,_,_,form⟩:=pure
  have h : PaperTerminalBridgeComplementSign.Complement (RingHomRealization.mapSignature phi q) := by
    rw [form]
    norm_num [PaperTerminalBridgeComplementSign.Complement,entries,ge4,complementWord,funext_iff,Fin.forall_fin_succ]
  exact ⟨phi.injective h.1,phi.injective h.2.1,phi.injective h.2.2⟩

variable {s degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (a i.val)) (F : FixedField L degree)
variable (q : Signature L 4) (label : Fin s)
variable (literal : (⟨a label.val,H label⟩ : AnySignature L)=⟨4,q⟩)
variable (even : EvenSupport q) (first : (entries q).a≠0) (last : (entries q).x≠0)

include literal even first last in
theorem source : NoISparseComplementComplete.Outcome L H F := by
  rcases NoIQuaternaryReduction.source L H F q label literal even first last with good|hard|pure|comp
  · exact Or.inl good
  · exact Or.inr (Or.inl hard)
  · exact NoISparseComplementComplete.source L H F q even first last (pure_complement L.subtype q pure)
      ⟨1,one_ne_zero,by simpa only [one_mul] using
        (Gadget.realizes_of_mem (PaperTerminalBridgeDenseSemantic.family H) .disequality q ⟨label,literal⟩)⟩
  · obtain ⟨g,actual,ev,firstG,lastG,complement⟩:=comp
    exact NoISparseComplementComplete.source L H F g ev firstG lastG complement actual

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIQuaternaryPureReduction
end
