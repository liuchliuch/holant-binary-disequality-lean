import Holant.Proofs.Hardness.GeneralEODEQPairingTemplates
import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyNative
import Holant.Proofs.Algorithms.RawArityTransport
import Holant.Proofs.Algorithms.ControlledReduction
import Holant.Proofs.Platonic.PhysicalCostComposition

/-! The complete physical source for arbitrary pairing-restricted CSPs when
the original target alphabet contains DEQ4. Restriction is performed by actual
filter graphs. In particular, no support-cover premise is made on the original
rows, and all target queries retain the original table and fixed-field codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQPairingSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose
namespace M
export GeneralEODEQPairingTemplates (family sourceArity coordinates tables inputEncoding value
  arity_eq signature_exact controlled)
end M
namespace C
export GeneralEOPairedCSPFamilyNative (totalValue totalControlled)
export GeneralEOPairedCSPCycles (Covers compress)
end C
namespace A
export Holant.LocalDrafts.MainChain.RawArityTransport (input computes signatures denote)
end A
namespace L
export Holant.LocalDrafts.Tractability.EOEvaluation.PairLift (Compatible)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {a : ℕ → ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s 1 a)
variable (P : (i : Fin s) → OrientedPerfectPairing (a i.val))
variable (e : Fin s)
variable (hE : (⟨a e.val,M.family F T e⟩ : AnySignature K) = ⟨4,ExactTwoSignatures.E⟩)

def restricted (i : Fin s) : Signature K (a i.val) :=
  fun x => if L.Compatible (P i) x then M.family F T i x else 0

theorem covers (i : Fin s) : C.Covers (P i) (restricted F T P i) := by
  intro x hx
  by_contra hn
  exact hx (ite_eq_right hn)

theorem compress_restricted (i : Fin s) :
    C.compress (P i) (restricted F T P i) = C.compress (P i) (M.family F T i) := by
  funext z
  apply ite_eq_left
  intro j
  simp [OrientedPerfectPairing.word]

theorem arities (i : Fin s) : a i.val = M.sourceArity P F T e hE i.val :=
  congrFun (M.arity_eq (M.family F T) P e hE).symm i.val

omit [Field K] [Algebra ℚ K] in
private theorem transport_signature {m n : ℕ} (f : Signature K m) (g : Signature K n)
    (eqn : (⟨n,g⟩ : AnySignature K) = ⟨m,f⟩) (h : m=n) :
    g = fun x => f (fun j => x (Fin.cast h j)) := by
  cases eqn
  rfl

theorem decoded_restricted
    (native : ∀ j x y, F.decode (T.edge j x y) = Signature.disequality x y) :
    (fun i x => F.decode (M.coordinates P F T e hE i x)) =
      A.signatures (arities F T P e hE) (restricted F T P) := by
  funext i
  exact transport_signature _ _ (M.signature_exact P F T e hE native i) _

theorem retag_value
    (native : ∀ j x y, F.decode (T.edge j x y) = Signature.disequality x y)
    (r : GeneralEOPairedCSPNative.TargetInput (s:=s) (arity:=a)) :
    GeneralEOPairedCSPNative.targetValue F (restricted F T P) r =
      M.value P F T e hE (A.input (arities F T P e hE) r) := by
  rw [GeneralEOPairedCSPNative.target_semantics]
  unfold M.value
  rw [ExactSignatureTables.evaluate_eq_decoded]
  change _ = ((A.input (arities F T P e hE) r).val.realize
    (A.input (arities F T P e hE) r).property
    (fun i x => F.decode (M.coordinates P F T e hE i x))
    (fun j x y => F.decode (T.edge j x y))).denote Fin.elim0
  rw [decoded_restricted F T P e hE native]
  have hn : (fun j x y => F.decode (T.edge j x y)) =
      (fun _ => Signature.disequality) :=
    funext (fun j => funext (fun x => funext (fun y => native j x y)))
  rw [hn]
  exact (A.denote (arities F T P e hE) (restricted F T P) _ r).symm

def retagControlled
    (native : ∀ j x y, F.decode (T.edge j x y) = Signature.disequality x y) :
    LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
      (M.inputEncoding P F T e hE) F.encoding
      (GeneralEOPairedCSPNative.targetValue F (restricted F T P)) (M.value P F T e hE) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq
    (A.computes (arities F T P e hE)) (identityComputes F.encoding)
    ((M.tables P F T e hE).outputBound F) _ (retag_value F T P e hE native)

theorem totalValue_eq : C.totalValue (restricted F T P) P = C.totalValue (M.family F T) P := by
  funext r
  unfold C.totalValue
  have h : (fun i => C.compress (P i) (restricted F T P i)) =
      (fun i => C.compress (P i) (M.family F T i)) := funext (compress_restricted F T P)
  rw [h]

/-- An actual executed compiler from the entire mixed pairing-restricted CSP
alphabet to the unchanged original Holant table. -/
def controlled
    (native : ∀ j x y, F.decode (T.edge j x y) = Signature.disequality x y) :
    LengthControlledOracleReduction (GeneralEOPairedCSPFamilyRaw.encoding s) F.encoding
      (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
      (C.totalValue (M.family F T) P) (T.evaluate F) := by
  rw [←totalValue_eq F T P]
  exact Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (C.totalControlled F (restricted F T P) P (covers F T P))
    (Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
      (retagControlled F T P e hE native) (M.controlled P F T e hE))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQPairingSource
