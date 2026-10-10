import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinOrdinaryAttach
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinOrdinaryHTransport
import Holant.Certificates.EqualityQuaternary.ExoticKleinSource

/-! The exotic orbit word is implemented by ordinary equality-edge graphs
in Hadamard coordinates. Every native dressing uses its transformed actual
binary and the transformed native-X row Z/2, with the exact factor 1/4. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinOrdinaryOrbit
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Certificates.EqualityQuaternary
open Holant.Projective.CyclicDressing
namespace A
export GlobalCloseCompletionKleinOrdinaryAttach (binary attach attach_denote labels exact ordinary)
end A
namespace C
export BinaryInterpolation.Chains (reindex reindex_denote)
end C
namespace O
export Klein.Orbit (Op actualAct actualRun auxiliary swapPorts)
end O
namespace T
export GlobalCloseCompletionKleinOrdinaryHTransport (H zHalf dress_transport site_scalar action_reindex)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {F : SignatureFamily AlgebraicComplex} (reps : Klein.Representatives F .exotic)

def step : O.Op → Network AlgebraicComplex 4 → Network AlgebraicComplex 4
  | .dress i j,N => A.attach (A.attach N i T.zHalf) i (transport T.H (reps.matrix (O.auxiliary j)))
  | .swap i,N => C.reindex N (O.swapPorts i)

def stepScalar : O.Op → AlgebraicComplex
  | .dress _ _ => 1/4
  | .swap _ => 1

def run : List O.Op → Network AlgebraicComplex 4 → Network AlgebraicComplex 4
  | [],N => N
  | op::ops,N => run ops (step reps op N)

def scalar : List O.Op → AlgebraicComplex
  | [] => 1
  | op::ops => scalar ops*stepScalar op

theorem scalar_nonzero (ops : List O.Op) : scalar ops≠0 := by
  induction ops with
  | nil => exact one_ne_zero
  | cons op ops ih =>
    apply mul_ne_zero ih
    cases op <;> norm_num [stepScalar]

theorem action_scale {n : ℕ} (U : InvertibleKernel) (c : AlgebraicComplex)
    (q : Signature AlgebraicComplex n) :
    U.action (fun x=>c*q x)=fun x=>c*U.action q x := by
  funext x
  simp only [InvertibleKernel.action,Signature.coordinateAction,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem step_denote (op : O.Op) (N : Network AlgebraicComplex 4)
    (q : Signature AlgebraicComplex 4) (c : AlgebraicComplex)
    (form : N.denote=fun x=>c*T.H.symm.action q x) :
    (step reps op N).denote=fun x=>(stepScalar op*c)*T.H.symm.action (O.actualAct reps op q) x := by
  cases op with
  | dress i j =>
    simp only [step,A.attach_denote,form,T.site_scalar,T.dress_transport,O.actualAct]
    funext x
    change c*((1/4)*_) = ((1/4)*c)*_
    ring
  | swap i =>
    rw [step,C.reindex_denote,form]
    have h := T.action_reindex T.H.symm (O.swapPorts i) q
    funext x
    have hx := congrFun h x
    change c*Tensor.reindex (O.swapPorts i) (T.H.symm.action q) x=(1*c)*T.H.symm.action (Tensor.reindex (O.swapPorts i) q) x
    rw [hx,one_mul]

theorem run_denote (ops : List O.Op) (N : Network AlgebraicComplex 4)
    (q : Signature AlgebraicComplex 4) (c : AlgebraicComplex)
    (form : N.denote=fun x=>c*T.H.symm.action q x) :
    (run reps ops N).denote=fun x=>(scalar ops*c)*T.H.symm.action (O.actualRun reps ops q) x := by
  induction ops generalizing N q c with
  | nil => simpa only [run,scalar,O.actualRun,one_mul] using form
  | cons op ops ih =>
    rw [run,ih _ _ _ (step_denote reps op N q c form)]
    simp only [O.actualRun]
    funext x
    change (scalar ops*(stepScalar op*c))*_=((scalar ops*stepScalar op)*c)*_
    ring

theorem step_ordinary (op : O.Op) (N : Network AlgebraicComplex 4)
    (input : ∀e,N.edge e=Signature.equality) :
    ∀e,(step reps op N).edge e=Signature.equality := by
  cases op with
  | dress i j => exact A.ordinary _ _ _ (A.ordinary _ _ _ input)
  | swap i => exact input

theorem run_ordinary (ops : List O.Op) (N : Network AlgebraicComplex 4)
    (input : ∀e,N.edge e=Signature.equality) :
    ∀e,(run reps ops N).edge e=Signature.equality := by
  induction ops generalizing N with
  | nil => exact input
  | cons op ops ih => exact ih _ (step_ordinary reps op N input)

section Labels
variable {s : ℕ} {a : ℕ→ℕ} (H : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (z : Fin s) (zLiteral : (⟨a z.val,H z⟩ : AnySignature AlgebraicComplex)=⟨2,A.binary T.zHalf⟩)
variable (row : Fin 4→Fin s) (rowLiteral : ∀j,
  (⟨a (row j).val,H (row j)⟩ : AnySignature AlgebraicComplex)=⟨2,A.binary (transport T.H (reps.matrix j))⟩)

def stepLabels (op : O.Op) (N : Network AlgebraicComplex 4) (L : Labelling N.shape s 1 a) :
    Labelling (step reps op N).shape s 1 a := match op with
  | .dress i j => A.labels H _ (A.labels H N L z T.zHalf zLiteral i)
      (row (O.auxiliary j)) _ (rowLiteral (O.auxiliary j)) i
  | .swap i => LabelledNetwork.reindex N L (O.swapPorts i)

theorem step_exact (op : O.Op) (N : Network AlgebraicComplex 4) (L : Labelling N.shape s 1 a)
    (input : LabelledNetwork.Exact H N L) :
    LabelledNetwork.Exact H (step reps op N) (stepLabels reps H z zLiteral row rowLiteral op N L) := by
  cases op with
  | dress i j => exact A.exact H _ _ _ _ _ _ (A.exact H N L z _ zLiteral i input)
  | swap i => exact input

def runLabels (ops : List O.Op) (N : Network AlgebraicComplex 4) (L : Labelling N.shape s 1 a) :
    Labelling (run reps ops N).shape s 1 a := match ops with
  | [] => L
  | op::ops => runLabels ops (step reps op N) (stepLabels reps H z zLiteral row rowLiteral op N L)

theorem run_exact (ops : List O.Op) (N : Network AlgebraicComplex 4) (L : Labelling N.shape s 1 a)
    (input : LabelledNetwork.Exact H N L) :
    LabelledNetwork.Exact H (run reps ops N) (runLabels reps H z zLiteral row rowLiteral ops N L) := by
  induction ops generalizing N with
  | nil => exact input
  | cons op ops ih => exact ih _ _ (step_exact reps H z zLiteral row rowLiteral op N L input)
end Labels


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinOrdinaryOrbit
end
