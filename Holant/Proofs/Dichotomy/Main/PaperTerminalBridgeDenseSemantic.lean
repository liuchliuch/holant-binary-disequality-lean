import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeDenseInfinite
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeAntiGroup
import Holant.Complexity.BinaryInterpolation.Chains.DirectMacro

/-! Semantic actual antidiagonals of infinite ratio supply the labelled
native macro required by the exact interpolation source. No isolated wire
can have nontrivial ratio; all literal original vertices are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseSemantic
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.OpenNetworkComposition.FactorFreeNormalization
namespace S
export NativeAntiTargetSource (Output base)
end S
namespace A
export NativeAntiTargetAlgebra (anti)
export PaperTerminalBridgeAntiGroup (Available)
end A
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (binarySignature labellingOfUses binary_hasXFactor_scalar)
export GeneralCancellationCapPin (antiTensor)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {K : Type} [Field K] [NumberField K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)

def family : SignatureFamily K := Set.range (fun i=>(⟨a i.val,H i⟩ : AnySignature K))

theorem anti_eq (p q : K) : C.binarySignature (A.anti p q)=C.antiTensor p q := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [C.binarySignature,A.anti,C.antiTensor,h0,h1]

theorem noXFactor (t : K) (notone : t≠1) : NoXFactor (C.antiTensor 1 t) := by
  intro factor
  rw [←anti_eq] at factor
  obtain ⟨c,value⟩ := C.binary_hasXFactor_scalar (A.anti 1 t) factor
  have left := congrFun₂ value false true
  have right := congrFun₂ value true false
  simp only [A.anti,Holant.Certificates.MatchingContractionClosure.X,
    Signature.disequality,Matrix.smul_apply,smul_eq_mul] at left right
  norm_num at left right
  exact notone (right.trans left.symm)

theorem output (t : K) (actual : A.Available (family H) t) (notone : t≠1) :
    ∃c : K,c≠0 ∧ ∃N : S.Output H 2,
      N.network.denote=C.binarySignature (A.anti c (c*t)) := by
  obtain ⟨c,hc,N,hv,he,hn⟩ := realizesUpTo_exists_ordinary actual (noXFactor t notone)
  let labels := C.labellingOfUses a H N hv (0 : Fin 1)
  let out : S.Output H 2 := ⟨N,labels,fun v=>Classical.choose_spec (hv v),he⟩
  refine ⟨c,hc,out,?_⟩
  change N.denote=_
  rw [hn,anti_eq]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [C.antiTensor,h0,h1]

variable (M : Signature K 4) (label : Fin s)
variable (literal : (⟨a label.val,H label⟩ : AnySignature K)=⟨4,M⟩)
variable (even : EvenSupport M) (dense : StableDenseParityAlgebra.Dense M)
variable (different : ¬PaperTerminalBridgeDenseOrders.EqualProducts M)
variable (t : K) (nonzero : t≠0) (actual : A.Available (family H) t)
variable (infinite : ¬IsOfFinOrder t)

include literal even dense different nonzero actual infinite in
theorem countingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding ((S.base H F).evaluate F) := by
  have notone : t≠1 := by rintro rfl;exact infinite (isOfFinOrder_iff_pow_eq_one.mpr ⟨1,by omega,by simp⟩)
  obtain ⟨c,hc,N,form⟩ := output H t actual notone
  apply PaperTerminalBridgeDenseInfinite.countingHard H F M label literal even dense different
    N c (c*t) hc (mul_ne_zero hc nonzero) _ form
  intro n hn root
  apply infinite
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨n,hn,?_⟩
  have ratio : c*t/c=t := by field_simp
  rwa [ratio] at root


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseSemantic
end
