import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2CurrentComplement
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SixPortProblem
import Holant.Pauli.ExoticKlein.SixPortSetup

/-! Exact literal I/X matching lines obtained from the actual order-two
complete group. The original coefficient and the actual matching ports remain
explicit; no normalized resource is inferred from projective membership. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2MatchingLines
open Holant Holant.Tractable Holant.Algebraic
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant.Pauli.ExoticKlein.SixPort
open GlobalCloseCompletionC2SixPortProblem
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false
variable {L : Type*} [Field L] [NumberField L]
variable (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (hI : RetainsIdentity F) (cardTwo : Nat.card (completeGroup F torsion) = 2)
include torsion hI cardTwo

theorem safe_binary_literal (B : Binary (K := L))
    (safe : SafeBinary (actualTransfers F) B) :
    ∃ p : Bool, ∃ c : L, c ≠ 0 ∧ B = c • originalC2Binary p := by
  obtain ⟨j,c,hc,he⟩ := safe_binary_eq_representative F torsion B safe
  obtain ⟨p,d,hd,hm⟩ := c2_actual_binary F torsion hI cardTwo
    (actualRepresentative F torsion j) (actualRepresentative_actual F torsion j)
  exact ⟨p,c*d,mul_ne_zero hc hd,by rw [he,hm,smul_smul]⟩

theorem matching_literal {I : Type*} (f : Tensor L I) (nonzero : f ≠ 0)
    (matching : MatchingOrZero (actualTransfers F) f) :
    ∃ k : ℕ, ∃ ports : (Fin k × Bool) ≃ I, ∃ label : Fin k → Bool,
    ∃ c : L, c ≠ 0 ∧ f = productValue ports (fun i => originalC2Binary (label i)) c := by
  obtain ⟨M,valid,scalarNonzero,rfl⟩ := matching.resolve_left nonzero
  choose label coeff live equation using fun i =>
    safe_binary_literal F torsion hI cardTwo (M.matrix i) (valid i)
  refine ⟨M.edges,M.ports,label,M.scalar * ∏ i,coeff i,
    mul_ne_zero scalarNonzero (Finset.prod_ne_zero_iff.mpr (fun i _ => live i)),?_⟩
  funext w
  simp only [Presentation.tensor,productValue,equation,Matrix.smul_apply,smul_eq_mul,
    Finset.prod_mul_distrib]
  ring

omit torsion hI cardTwo in
theorem four_port_lines : ∀ (ports : Fin 2 × Bool → Fin 4), Function.Bijective ports →
    ∀ p : Fin 2 → Bool, ∃ j : Fin 12, ∀ w : Fin 16,
    (((wordEquiv 4).symm w (ports (0,false)) ^^ (wordEquiv 4).symm w (ports (0,true))) = p 0 ∧
      ((wordEquiv 4).symm w (ports (1,false)) ^^ (wordEquiv 4).symm w (ports (1,true))) = p 1) ↔
      w ∈ cardSupport j := by
  decide +kernel

omit [NumberField L] torsion hI cardTwo in
theorem binary_value (p a b : Bool) : originalC2Binary (L := L) p a b =
    if (a ^^ b) = p then 1 else 0 := by
  cases p <;> cases a <;> cases b <;>
    simp [originalC2Binary,X,Signature.disequality]

/-- The finite twelve-line dictionary covers the actual four-port matching,
including zero, over the same original coefficient field. -/
theorem matching_four_line (f : Signature L 4)
    (matching : MatchingOrZero (actualTransfers F) f) :
    ∃ j : Fin 12, ∃ c : L, ∀ w : Fin 16,
      f ((wordEquiv 4).symm w) = c * (if w ∈ cardSupport j then 1 else 0) := by
  by_cases zero : f = 0
  · exact ⟨0,0,by intro w; simp [zero]⟩
  obtain ⟨k,ports,p,c,_hc,equation⟩ := matching_literal F torsion hI cardTwo f zero matching
  have size := Fintype.card_congr ports
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at size
  have hk : k = 2 := by omega
  subst k
  obtain ⟨j,shape⟩ := four_port_lines ports ports.bijective p
  refine ⟨j,c,?_⟩
  intro w
  rw [equation]
  simp only [productValue,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,binary_value]
  simp only [←shape w]
  split_ifs <;> simp_all

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2MatchingLines
end
