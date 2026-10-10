import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2CanonicalPrime
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2OrdinaryCharts
import Holant.Proofs.Algorithms.PrimalityInterfaces
import Holant.Certificates.EqualityQuaternary.C2FirstFlip
import Holant.Certificates.EqualityQuaternary.CoordinatePrimality

/-! Every real port/Z chart preserves actual tensor primality. The checked
prime chart consumer consequently supplies Eq4 or closes the whole table;
no selected-row Affine conclusion is treated as a terminal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2PrimeCharts
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
open Holant.Certificates.EqualityQuaternary
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (Z)
end T
namespace C
export GlobalCloseCompletionC2Q4Charts (phase flip permutation chart)
end C
namespace O
export PaperControlled.C2OrdinaryCharts (phaseMacro mapped_phase chartMacro mapped_chart)
end O
namespace P
export PaperControlled.C2CanonicalPrime (Outcome shape)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 16384
set_option Elab.async false

theorem phase_prime (b : Bool) (f : Signature AlgebraicComplex 4) (prime : TensorPrime f) : TensorPrime (C.phase b f) := by
  cases b
  · have h : C.phase false f=f := by funext x;simp [C.phase]
    rw [h]
    exact prime
  · have inverse : ∀i : Fin 4,Kernel.mul (if i=0 then (T.Z (K:=AlgebraicComplex)) else Signature.equality)
        (if i=0 then (T.Z (K:=AlgebraicComplex)) else Signature.equality)=Signature.equality := by
      intro i
      by_cases hi : i=0
      · simp only [if_pos hi]
        funext a b
        cases a <;> cases b <;> simp [Kernel.mul_apply,T.Z,Signature.equality]
      · simp only [if_neg hi,Kernel.equality_mul]
    have h := prime_coordinateAction prime (fun i=>if i=0 then (T.Z (K:=AlgebraicComplex)) else Signature.equality)
      (fun i=>if i=0 then (T.Z (K:=AlgebraicComplex)) else Signature.equality) inverse
    rw [←Klein.Orbit.site_coordinate] at h
    have equation : Klein.Orbit.site (T.Z (K:=AlgebraicComplex)) 0 f=C.phase true f := by
      funext x
      have hu : Function.update x 0 (x 0)=x := Function.update_eq_self 0 x
      cases h0 : x 0
      all_goals
        rw [h0] at hu
        simp [Klein.Orbit.site,T.Z,C.phase,h0,hu]
    rwa [equation] at h

variable {s r degree : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable (F : FixedField K degree) (H : (i : Fin r)→Signature K (b i.val))
variable (back : LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (z : Fin r) (literal : (⟨b z.val,H z⟩ : AnySignature K)=⟨2,fun x=>T.Z (x 0) (x 1)⟩)

theorem phaseMacro_prime (choice : Bool) (N : Macro H 4)
    (prime : Prime (⟨4,N.network.denote⟩ : AnySignature K)) :
    Prime (⟨4,(O.phaseMacro K H z literal choice N).network.denote⟩ : AnySignature K) := by
  have mapped : Prime (⟨4,RingHomRealization.mapSignature K.subtype N.network.denote⟩ : AnySignature AlgebraicComplex) :=
    (prime_mapSignature_iff (K.subtype) (⟨4,N.network.denote⟩ : AnySignature K)).mpr prime
  have tensor := phase_prime choice _ ((PrimalityInterfaces.retained_equality_prime _).mp mapped)
  have result := (PrimalityInterfaces.retained_equality_prime _).mpr tensor
  rw [←O.mapped_phase K H z literal choice N] at result
  exact (prime_mapSignature_iff (K.subtype) (⟨4,(O.phaseMacro K H z literal choice N).network.denote⟩ : AnySignature K)).mp result

theorem chartMacro_prime (j : Fin 8) (N : Macro H 4)
    (prime : Prime (⟨4,N.network.denote⟩ : AnySignature K)) :
    Prime (⟨4,(O.chartMacro K H z literal j N).network.denote⟩ : AnySignature K) :=
  phaseMacro_prime K H z literal (C.flip j) (N.reindex (C.permutation j))
    (GlobalCloseCompletionC2SparsePrimeAnchors.reindex_prime H N prime _)

include back literal in
theorem classified (N : Macro H 4) (v : Fin 8→AlgebraicComplex)
    (form : RingHomRealization.mapSignature K.subtype N.network.denote=
      sourceKBasis.action (GlobalCloseCompletionC2Q4UnionCurrent.tensor v))
    (accepted : GlobalCloseCompletionC2Q4Union.Accepted (fun i=>(v i:ℂ)))
    (prime : Prime (⟨4,N.network.denote⟩ : AnySignature K)) : P.Outcome G K H := by
  obtain ⟨j,shape⟩ := GlobalCloseCompletionC2Q4Charts.accepted_chart v accepted
  exact P.shape G K F H back z literal (O.chartMacro K H z literal j N)
    (by rw [O.mapped_chart K H z literal j N v form];exact shape) (chartMacro_prime K H z literal j N prime)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2PrimeCharts
end
