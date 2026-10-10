import Holant.Proofs.Closure.ClosureBStableCurrent
import Holant.Proofs.Closure.ClosureSixPortDescent

/-! Closed B six-port split from the actual CURRENT deck. The displayed B
edge and ordered phase substitution are proved before invoking the native-M
base. Both coefficient descents preserve the actual partition and normalize
only the returned split multiplier; no physical normalization is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureBStable
open Holant Holant.Tractable Holant.Algebraic Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.Dihedral.CompatibleClosure

namespace RH
export Holant.LocalDrafts.MainChain.RingHomRealization (mapSignature)
end RH

def complexPresentation {n : ℕ} (Q : Presentation Scalar (Fin n)) : Presentation ℂ (Fin n) where
  edges := Q.edges
  ports := Q.ports
  matrix e := (Q.matrix e).map ClosureMarkedDihedral.inclusion
  scalar := ClosureMarkedDihedral.inclusion Q.scalar

theorem complexPresentation_tensor {n : ℕ} (Q : Presentation Scalar (Fin n)) :
    (complexPresentation Q).tensor=RH.mapSignature ClosureMarkedDihedral.inclusion Q.tensor := by
  funext x
  simp only [complexPresentation,Presentation.tensor,Holant.Certificates.MatchingContractionClosure.productValue,
    RH.mapSignature,Matrix.map_apply,map_mul,map_prod]
  rfl

theorem algebraic_matching_complex {n m : ℕ} (positive : 0<m) (q : Signature Scalar n)
    (actual : q=0 ∨ ClosureSixPort.AlgebraicRootMatching m q) :
    RH.mapSignature ClosureMarkedDihedral.inclusion q=0 ∨
      ClosureSixPort.RootMatching m (RH.mapSignature ClosureMarkedDihedral.inclusion q) := by
  rcases actual with rfl | ⟨Q,member,scalar,rfl⟩
  · left; funext x; exact map_zero _
  · exact Or.inr ⟨complexPresentation Q,fun e => groupM_complex_root positive _ (member e),
      (map_ne_zero ClosureMarkedDihedral.inclusion).mpr scalar,(complexPresentation_tensor Q).symm⟩

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

abbrev complexTransformed {n : ℕ} (f : Signature (OI.K G) n) : Signature ℂ n :=
  RH.mapSignature ClosureMarkedDihedral.inclusion (transformed G f)

theorem complexTransformed_nonzero {n : ℕ} (f : Signature (OI.K G) n) (nonzero : f≠0) :
    complexTransformed G f≠0 := by
  intro zero
  apply transformed_nonzero G f nonzero
  funext x
  apply ClosureMarkedDihedral.inclusion.injective
  simpa only [RH.mapSignature,map_zero,Pi.zero_apply] using congrFun zero x

/-- Every complex phase is lifted internally, with the exact phase value.
Zero cards remain zero, and nonzero cards keep their actual product ports. -/
theorem complex_ordered_root_deck {n : ℕ} (f : Signature (OI.K G) (n+2))
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)
    (e : Equiv.Perm (Fin (n+2))) (p : Bool) (t : ℂ) (root : t^N.selected.m=1) :
    Signature.contract (Holant.Dihedral.EndpointParallelogram.phaseKernel p t)
      (Tensor.reindex e.symm (complexTransformed G f))=0 ∨
      ClosureSixPort.RootMatching N.selected.m
        (Signature.contract (Holant.Dihedral.EndpointParallelogram.phaseKernel p t)
          (Tensor.reindex e.symm (complexTransformed G f))) := by
  let lifted := CyclicBoundary.AlgebraicRepresentatives.liftRoot
    (by have := N.selected.range; omega : 0<N.selected.m) ⟨t,root⟩
  have current := algebraic_matching_complex (by have := N.selected.range; omega) _
    (ordered_root_deck G P torsion N f stable e p lifted)
  have kernel := ClosureSixPort.compatibleM_complex p lifted.val
  have value : (lifted.val : ℂ)=t := rfl
  rw [value] at kernel
  have exactCard : RH.mapSignature ClosureMarkedDihedral.inclusion
      (Signature.contract (M p lifted.val) (Tensor.reindex e.symm (transformed G f)))=
      Signature.contract (Holant.Dihedral.EndpointParallelogram.phaseKernel p t)
        (Tensor.reindex e.symm (complexTransformed G f)) := by
    funext x
    simp only [RH.mapSignature,Signature.contract,Tensor.reindex,map_sum,map_mul]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    have entry := congrFun (congrFun kernel u) v
    change ClosureMarkedDihedral.inclusion ((M p lifted.val) u v)=_ at entry
    rw [entry]
  rw [exactCard] at current
  exact current

set_option backward.isDefEq.respectTransparency false in
theorem split_to_original {n : ℕ} (f : Signature (OI.K G) n) (nonzero : f≠0)
    {left right : AnySignature ℂ}
    (split : ProperSplit (⟨n,complexTransformed G f⟩ : AnySignature ℂ) left right) :
    ∃ A : Signature (OI.K G) left.1, ∃ B : Signature (OI.K G) right.1,
      ∃ result : ProperSplit (⟨n,f⟩ : AnySignature (OI.K G)) ⟨left.1,A⟩ ⟨right.1,B⟩,
        result.ports=split.ports ∧ result.scale=1 := by
  obtain ⟨A,B,algebraic,ports,unit⟩ := ClosureSixPort.exact_split_descent
    ClosureMarkedDihedral.inclusion ⟨n,transformed G f⟩
    (transformed_nonzero G f nonzero) split
  let originalMapped : ProperSplit
      (mapSignature (ClosureSourceRows.embedding G) (⟨n,f⟩ : AnySignature (OI.K G)))
      (ClosureFactorTreeAction.signature basisB ⟨left.1,A⟩)
      (ClosureFactorTreeAction.signature basisB ⟨right.1,B⟩) := by
    let acted := ClosureFactorTreeAction.split basisB algebraic
    exact {
      left_pos := algebraic.left_pos
      right_pos := algebraic.right_pos
      ports := algebraic.ports
      scale := algebraic.scale
      equation := by
        have equation := acted.equation
        simp only [acted,ClosureFactorTreeAction.signature,transformed,
          ClosureFactorTreeAction.split_ports,ClosureFactorTreeAction.split_scale,
          InvertibleKernel.action_symm_action] at equation
        funext x
        have point := congrFun equation x
        change ClosureSourceRows.embedding G (f x)=_ at point
        exact point }
  obtain ⟨C,D,original,exactPorts,exactUnit⟩ := ClosureSixPort.exact_split_descent
    (ClosureSourceRows.embedding G) ⟨n,f⟩ nonzero originalMapped
  exact ⟨C,D,original,exactPorts.trans ports,exactUnit⟩

include N in
/-- Actual CURRENT B stability, including all zero phases, produces a genuine
original-field 1+5 or 2+4 split without a supplied sector classification. -/
theorem current_six_split (f : Signature (OI.K G) 6) (nonzero : f≠0)
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    ∃ left right : AnySignature (OI.K G),
      ((left.1=1 ∧ right.1=5) ∨ (left.1=2 ∧ right.1=4)) ∧
      ∃ split : ProperSplit (⟨6,f⟩ : AnySignature (OI.K G)) left right,split.scale=1 := by
  have deck : ClosureSixPort.OrderedRootDeck N.selected.m (complexTransformed G f) := by
    intro e p t root
    have h := complex_ordered_root_deck G P torsion N f stable e p t root
    have identity : ClosureSixPort.phaseCard (complexTransformed G f) e p t=
        Signature.contract (Holant.Dihedral.EndpointParallelogram.phaseKernel p t)
          (Tensor.reindex e.symm (complexTransformed G f)) := by
      rw [ClosureSixPort.phaseCard_actual]
      funext x
      simp only [Holant.Dihedral.EndpointParallelogram.card,Signature.contract,Tensor.reindex,one_mul]
    rw [identity]
    exact h
  obtain ⟨left,right,arity,⟨split⟩⟩ := ClosureSixPort.direct_six_port_split N.selected.range
    (complexTransformed G f) (complexTransformed_nonzero G f nonzero) deck
  obtain ⟨A,B,result,_,unit⟩ := split_to_original G f nonzero split
  exact ⟨⟨left.1,A⟩,⟨right.1,B⟩,arity,result,unit⟩

include N in
theorem current_six_not_prime (f : Signature (OI.K G) 6) (nonzero : f≠0)
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    ¬Prime (⟨6,f⟩ : AnySignature (OI.K G)) := by
  obtain ⟨left,right,_,split,_⟩ := current_six_split G P torsion N f nonzero stable
  exact fun prime => prime.2 ⟨left,right,⟨split⟩⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureBStable
