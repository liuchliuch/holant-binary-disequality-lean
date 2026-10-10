import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicCurrentComplement
import Holant.Proofs.Closure.ClosureCyclicCurrentUnary

/-! Any actual quaternary has either its genuine cyclic complement symmetry,
or an actual nonzero singular raw binary. No stable-deck premise is imposed
on the output of a cyclic endpoint gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicActualDeck
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] [NumberField K]
variable (F : SignatureFamily K) (torsion : ResidualTorsion F) (hI : RetainsIdentity F)

theorem actual_binary_matching (g : Signature K 2)
    (actual : Gadget.Realizes F .disequality g) (nonzero : Matrix.det (binaryMatrix g)≠0) :
    MatchingOrZero (actualTransfers F) g := by
  refine Or.inr ⟨singleBinaryPresentation (binaryMatrix g),?_,one_ne_zero,?_⟩
  · intro i
    change transfer (binaryMatrix g)∈actualTransfers F
    refine ⟨binaryMatrix g,⟨?_,nonzero⟩,1,one_ne_zero,?_⟩
    · simpa only [binarySignature_binaryMatrix] using actual
    · simp
  · rw [singleBinaryPresentation_tensor,binarySignature_binaryMatrix]

include torsion hI in
theorem stable_or_singular (f : Signature K 4) (actual : Gadget.Realizes F .disequality f) :
    (∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) ∨
      ∃g : Signature K 2,g≠0 ∧ Gadget.Realizes F .disequality g ∧ Matrix.det (binaryMatrix g)=0 := by
  classical
  by_cases bad : ∃key : RawCardKey 2 (completeGroup F torsion),
      rawCard F torsion f key≠0 ∧ Matrix.det (binaryMatrix (rawCard F torsion f key))=0
  · obtain ⟨key,live,singular⟩ := bad
    exact Or.inr ⟨_,live,rawCard_realizes_exact F torsion hI (by norm_num) f actual key,singular⟩
  · left
    rintro g (rfl|⟨key,rfl⟩)
    · exact Or.inl rfl
    · by_cases zero : rawCard F torsion f key=0
      · exact Or.inl zero
      · exact actual_binary_matching F _ (rawCard_realizes_exact F torsion hI (by norm_num) f actual key)
          (fun singular=>bad ⟨key,zero,singular⟩)

include torsion hI in
theorem complement_or_singular (phi : K→+*ℂ)
    (cyclic : IsCyclic (completeGroup (RingHomRealization.mapFamily phi F)
      (ClosureFieldBridgeGroups.mappedTorsion phi F torsion)))
    (f : Signature K 4) (actual : Gadget.Realizes F .disequality f) :
    (∀x,f x=f (fun i=>!(x i))) ∨
      ∃g : Signature K 2,g≠0 ∧ Gadget.Realizes F .disequality g ∧ Matrix.det (binaryMatrix g)=0 := by
  rcases stable_or_singular F torsion hI f actual with stable|singular
  · exact Or.inl (GlobalCloseCompletionCyclicCurrentComplement.current_complement F torsion hI phi cyclic f stable)
  · exact Or.inr singular

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (f : Signature (OI.K G) 2) (nonzero : f≠0)
variable (actual : Gadget.Realizes P.family .disequality f)

abbrev palette : Palette G := ProgrammeSaturation.palette G P ⟨2,f⟩ nonzero (by change 0<2;decide) actual

theorem retains_old : P.family⊆(palette G P f nonzero actual).family :=
  ProgrammeSaturation.retains_old G P _ _ _ _

theorem retained_unary (singular : Matrix.det (binaryMatrix f)=0) :
    RetainedUnary (palette G P f nonzero actual).family := by
  let Q := palette G P f nonzero actual
  let tree := RetainedFactorCatalogue.tree G (⟨2,f⟩ : AnySignature (OI.K G)) nonzero
  obtain ⟨g,hg,size⟩ := ClosureCyclicCurrent.singular_binary_unary_leaf f tree singular
  let j := RetainedFactorCatalogue.rootLabel G P (⟨2,f⟩ : AnySignature (OI.K G)) nonzero
  have saved : (⟨⟨Q.arity j.val,Q.table j⟩,Q.trees j⟩ : TreeOccurrence (OI.K G))=⟨⟨2,f⟩,tree⟩ :=
    ProgrammeSaturation.root_saved G P _ _ _ _
  have leaves := congrArg (fun z : TreeOccurrence (OI.K G)=>z.2.leaves) saved
  have kept : g∈(Q.trees j).leaves := by
    change (Q.trees j).leaves=tree.leaves at leaves
    rw [leaves]
    exact hg
  obtain ⟨i,literal⟩ := Q.leavesRetained j g kept
  have prime := tree.leaves_prime g hg
  obtain ⟨n,u⟩ := g
  dsimp only at size
  subst n
  exact ⟨u,⟨i,literal⟩,prime.1⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicActualDeck
end
