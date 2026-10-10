import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2WalshFlat
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2HigherStructure

/-! The genuine six-port prime exclusion from literal C2 Walsh coefficients.
A cross-pair card of the generic weighted exception has values2c and2cr₂.
Literal I/X flat squares force r₂²=1, contradicting κr₂²=1 and κ≠1.
The exact finite DAG remains an independent stronger literal classification. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SixPortPrime
open Holant Holant.Tractable
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.CoefficientAtlas Holant.ReedMuller.WeightTwoIntegration
open Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open GlobalCloseCompletionC2TensorMatching GlobalCloseCompletionC2SafeSymmetry
open GlobalCloseCompletionC2HigherDeck GlobalCloseCompletionC2HigherStructure
namespace W
export GlobalCloseCompletionC2WalshFlat (literal_square walsh_contract)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 16384
set_option Elab.async false

def crossOrder : Equiv.Perm (Fin 6) := Equiv.swap 1 2

def cross (f : Signature ℂ 6) : Signature ℂ 4 :=
  Signature.contract Signature.equality (Tensor.reindex crossOrder.symm f)

theorem cross_safe (f : Signature ℂ 6) (safe : Safe f) : LiteralMatching (cross f) := by
  have h := safe crossOrder false
  have eqn : originalC2Binary (L:=ℂ) false=(Signature.equality : Kernel ℂ) := by
    funext a b
    cases a <;> cases b <;> rfl
  rw [eqn] at h
  exact h

theorem exceptional_walsh (f : Signature ℂ 6) (d : ExceptionalData) (c : ℂ)
    (form : f=fun x=>c*Signature.coordinateAction (fun _=>walshKernel) (ExceptionalTopology.paired d.h) x) :
    walsh f=fun x=>c*ExceptionalTopology.paired d.h x := by
  rw [form]
  change walsh (c • Signature.coordinateAction (fun _=>walshKernel) (ExceptionalTopology.paired d.h))=_
  rw [walsh_smul,walsh_of_physical]
  rfl

theorem cross_origin (f : Signature ℂ 6) (d : ExceptionalData) (c : ℂ)
    (form : walsh f=fun x=>c*ExceptionalTopology.paired d.h x) :
    walsh (cross f) (fun _=>false)=2*c := by
  rw [cross,W.walsh_contract,form]
  dsimp only
  rw [Signature.contract_equality]
  change 2*(c*1+c*0)=2*c
  ring

theorem cross_last (f : Signature ℂ 6) (d : ExceptionalData) (c : ℂ)
    (form : walsh f=fun x=>c*ExceptionalTopology.paired d.h x) :
    walsh (cross f) ![false,false,true,true]=2*c*d.r 2 := by
  rw [cross,W.walsh_contract,form]
  dsimp only
  rw [Signature.contract_equality]
  change 2*(c*d.r 2+c*0)=2*c*d.r 2
  ring

theorem not_exceptional (f : Signature ℂ 6) (safe : Safe f) : ¬ExceptionalForm f := by
  rintro ⟨d,p,c,hc,form⟩
  let g := Tensor.reindex p f
  have gs : Safe g := safe.reindex p
  have hg := exceptional_walsh g d c form
  have last := cross_last g d c hg
  have origin := cross_origin g d c hg
  have live : walsh (cross g) ![false,false,true,true]≠0 := by
    rw [last]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hc) (d.r_ne_zero 2)
  have squares := W.literal_square (cross g) (cross_safe g gs) _ live
  rw [last,origin] at squares
  have r2 : d.r 2 ^ 2=1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (mul_ne_zero (by norm_num : (2:ℂ)≠0) hc))
    simpa only [mul_pow,mul_one] using squares
  have eqn := d.square 2
  rw [r2,mul_one] at eqn
  exact d.kappa_ne_one eqn

theorem safe_not_prime (f : Signature ℂ 6) (prime : Prime (⟨6,f⟩ : AnySignature ℂ)) (safe : Safe f) : False := by
  by_cases edge : ∃u v,(weightGraph (walsh f)).Adj u v
  · rcases Holant.ReedMuller.WeightTwoIntegration.source_weight_two_structure
      ixGroup_group ixGroup_span representatives f prime.1 (by norm_num) (safe_deck f safe) edge with factor|exceptional
    · exact ((PrimalityInterfaces.retained_complex_prime f).mp prime).2 factor
    · exact not_exceptional f safe exceptional
  · have h0 := (safe_consistent f prime.1 (by norm_num) safe).constant_ne_zero
    let c : ℂ := (walsh f (fun _=>false))⁻¹
    have hc : c≠0 := inv_ne_zero h0
    let g := c • f
    have gs : Safe g := safe_smul f safe c
    have gp : Prime (⟨6,g⟩ : AnySignature ℂ) :=
      Holant.LocalDrafts.Hardness.FrozenFactorNormalization.prime_scaled (Units.mk0 c hc) prime
    have g0 : walsh g (fun _=>false)=1 := by rw [walsh_smul]; exact inv_mul_cancel₀ h0
    have empty : weightGraph (walsh g)=⊥ := by
      ext u v
      simp only [SimpleGraph.bot_adj,iff_false]
      rintro ⟨huv,hn⟩
      apply edge
      refine ⟨u,v,huv,?_⟩
      rw [walsh_smul] at hn
      exact (mul_ne_zero_iff.mp hn).2
    have size := (Holant.ReedMuller.SupportReconstruction.source_reed_muller_support
      ixGroup_group ixGroup_span representatives g gp.1 (by norm_num) g0 (safe_deck g gs) empty).2.2.1
    norm_num at size

variable {K : Type*} [Field K] [NumberField K]
theorem current_not_prime (F : SignatureFamily K) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (cardTwo : Nat.card (completeGroup F torsion)=2)
    (phi : K→+*ℂ) (f : Signature K 6) (prime : Prime (⟨6,f⟩ : AnySignature K))
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) : False :=
  safe_not_prime _ ((prime_mapSignature_iff phi _).mpr prime)
    ((current_safe F torsion hI cardTwo f stable).map phi)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SixPortPrime
end
