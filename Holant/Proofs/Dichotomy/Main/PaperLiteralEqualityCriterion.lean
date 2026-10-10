import Holant.Proofs.Dichotomy.Main.PaperBinaryDisequality

/-! Exact criterion for native-X evaluation on a finite original family.
Supplying a literal equality row makes the first theorem's retained family
identical to the original family; the native positive evaluator already works
on these exact original labels and their original coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperLiteralEqualityCriterion
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
abbrev family : SignatureFamily AlgebraicComplex :=
  Set.range (fun i=>(⟨a i.val,G i⟩ : AnySignature AlgebraicComplex))
abbrev Criterion := TractX (familyAction sourceKBasis (family G))
abbrev inputEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev presentation := OriginalFamily.presentation G KSourceTransport.nativeEdges
abbrev value := OriginalFamily.value G KSourceTransport.nativeEdges
abbrev Hard := Holant.LocalDrafts.CountingHardness.WitnessCountingHard
  (inputEncoding (s:=s) (a:=a)) (presentation G).encoding (value G)

theorem positive (criterion : Criterion G) :
    InFP (inputEncoding (s:=s) (a:=a)) (presentation G).encoding (value G) :=
  TractXCoreSource.native_inFP_of_KTractX G (family G) (fun i=>Set.mem_range_self i)
    (Set.finite_range _) criterion

variable (j : Fin s)
variable (literal : (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)=
  ⟨2,kernelSignature Signature.equality⟩)
include literal in
theorem retained_eq : BinaryDisequalityTractability.retainedFamily G=family G := by
  apply Set.union_eq_left.mpr
  rintro f hf
  obtain rfl:=Set.mem_singleton_iff.mp hf
  exact ⟨j,literal⟩

include literal in
theorem criterion_eq : PaperBinaryDisequality.Criterion G=Criterion G := by
  unfold PaperBinaryDisequality.Criterion
  rw [retained_eq G j literal]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperLiteralEqualityCriterion
end
