import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryLiteralSource
import Holant.Proofs.Hardness.GeneralOddNonisotropicFrame

/-! A genuine literal Z row reflects an isotropic nonzero ordinary unary to
an actual independent unary by one equality edge. The whole old table plus
this new unary is installed by the existing literal graph-adjoin programme.
Independence supplies source access; it is not identified with hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryIsotropicSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (tensor tensor_denote)
end C
namespace U
export GeneralOddNonisotropicFrame (norm)
end U
namespace L
export GlobalCloseCompletionUnaryLiteralSource (Output arity signatures tables source old old_literal unaryLabel unary_literal)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {r : ℕ} {b : ℕ→ℕ}

def z : Signature K 2 := fun x=>if x 0=x 1 then if x 0 then -1 else 1 else 0
def determinant (u v : Signature K 1) : K :=
  u (fun _=>false)*v (fun _=>true)-u (fun _=>true)*v (fun _=>false)
def reflect (N : Network K 1) (Z : Network K 2) : Network K 1 :=
  (C.tensor N Z).contract Signature.equality

theorem reflect_denote (N : Network K 1) (Z : Network K 2) (hZ : Z.denote=z) :
    (reflect N Z).denote=fun x=>if x 0 then -N.denote (fun _=>true) else N.denote (fun _=>false) := by
  funext x
  rw [reflect,Network.denote_contract,C.tensor_denote,hZ]
  simp only [Signature.contract_equality,Signature.tensor_apply]
  have left (v : Bool) :
      (fun i : Fin 1=>(Fin.cons v (Fin.cons v x) : Fin 3→Bool) (Fin.castAdd 2 i))=(fun _=>v) := by
    funext i; fin_cases i; rfl
  have right (v : Bool) :
      (fun i : Fin 2=>(Fin.cons v (Fin.cons v x) : Fin 3→Bool) (Fin.natAdd 1 i))=![v,x 0] := by
    funext i; fin_cases i <;> rfl
  simp only [left,right]
  cases x 0 <;> simp [z]

theorem isotropic_full (u : Signature K 1) (nonzero : u≠0) (isotropic : U.norm u=0) :
    u (fun _=>false)≠0 ∧ u (fun _=>true)≠0 := by
  have word (x : Fin 1→Bool) : x=(fun _=>x 0) := by
    funext i; exact congrArg x (Subsingleton.elim _ _)
  have full : ¬(u (fun _=>false)=0 ∧ u (fun _=>true)=0) := by
    rintro ⟨h0,h1⟩
    apply nonzero
    funext x
    rw [word x]
    cases x 0 <;> assumption
  constructor
  · intro h0
    have h1 : u (fun _=>true)^2=0 := by simpa [U.norm,h0] using isotropic
    exact full ⟨h0,sq_eq_zero_iff.mp h1⟩
  · intro h1
    have h0 : u (fun _=>false)^2=0 := by simpa [U.norm,h1] using isotropic
    exact full ⟨sq_eq_zero_iff.mp h0,h1⟩

theorem independent [CharZero K] (N : Network K 1) (Z : Network K 2) (hZ : Z.denote=z)
    (nonzero : N.denote≠0) (isotropic : U.norm N.denote=0) :
    determinant N.denote (reflect N Z).denote≠0 := by
  obtain ⟨h0,h1⟩ := isotropic_full N.denote nonzero isotropic
  rw [reflect_denote N Z hZ]
  have value : determinant N.denote
      (fun x=>if x 0 then -N.denote (fun _=>true) else N.denote (fun _=>false))=
      -2*N.denote (fun _=>false)*N.denote (fun _=>true) := by
    simp only [determinant,Bool.false_eq_true,ite_false,ite_true]
    ring
  rw [value]
  exact mul_ne_zero (mul_ne_zero (by norm_num) h0) h1

variable (H : (i : Fin r)→Signature K (b i.val))
variable (N : Network K 1) (NL : Labelling N.shape r 1 b)
variable (hN : LabelledNetwork.Exact H N NL) (ordinaryN : ∀e,N.edge e=Signature.equality)
variable (j : Fin r) (literal : (⟨b j.val,H j⟩ : AnySignature K)=⟨2,z⟩)

def zLabels : Labelling (Network.corolla (z (K:=K))).shape r 1 b where
  vertex _ := j
  vertex_arity _ := congrArg Sigma.fst literal
  edge e := Fin.elim0 e
def labels : Labelling (reflect N (Network.corolla (z (K:=K)))).shape r 1 b :=
  LabelledNetwork.contract _
    (LabelledNetwork.tensor N (Network.corolla z) NL (zLabels H j literal)) 0 Signature.equality
include hN in
theorem exact : LabelledNetwork.Exact H (reflect N (Network.corolla (z (K:=K)))) (labels H N NL j literal) :=
  LabelledNetwork.exact_tensor N (Network.corolla z) NL (zLabels H j literal) H hN (fun _=>literal)
include ordinaryN in
theorem ordinary : ∀e,(reflect N (Network.corolla (z (K:=K)))).edge e=Signature.equality := by
  intro e
  refine Fin.cases rfl (fun e=>?_) e
  change (Network.tensorFinite N (Network.corolla (z (K:=K)))).edge (finSumFinEquiv.symm e)=_
  cases finSumFinEquiv.symm e with
  | inl e=>exact ordinaryN e
  | inr e=>exact Fin.elim0 e

def output : L.Output H :=
  ⟨reflect N (Network.corolla z),labels H N NL j literal,exact H N NL hN j literal,ordinary N ordinaryN⟩

section Source
variable [Algebra ℚ K] {degree : ℕ} (F : FixedField K degree)
def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (r+1) 1 (L.arity H (output H N NL hN ordinaryN j literal))) F.encoding
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    ((QuaternaryOrdinaryCompanion.tables F (L.signatures F H (output H N NL hN ordinaryN j literal))).evaluate F)
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) :=
  L.source F H (output H N NL hN ordinaryN j literal)

end Source


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryIsotropicSource
end
