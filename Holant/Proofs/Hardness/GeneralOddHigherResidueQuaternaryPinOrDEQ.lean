import Holant.Proofs.Hardness.GeneralOddHigherResidueQuaternaryEndpoints
import Holant.Proofs.Hardness.GeneralOddHigherResidueQuaternaryJoin
import Holant.Proofs.Hardness.GeneralEOPinnedDescentNetwork
import Holant.Proofs.Hardness.ExactTwoSignatures

/-! Structural pin-or-DEQ production from the actual nonprimitive odd residue.
The original two-sided family supplies both minimal endpoint orientations.
Two nonzero endpoints of one terminal give scalar DEQ4 after d-2 physical
parallel X edges. Otherwise opposite pure terminals give a directed binary
pin after d-1 physical edges. No cancellation claim is used: the partial-join
denotation is evaluated exactly. Scalars are retained, not divided out. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHigherResidueQuaternaryPinOrDEQ
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.GeneralExtraction
open NamedContraction SupportDescent SupportCaps
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open GeneralOddUnaryOrdinary GeneralOddUnarySource
namespace M
export GeneralOddMinimalTerminal (Minimal endpoint noCuts)
end M
namespace J
export GeneralOddHigherResidueQuaternaryPartialJoin
  (network finite Edges denote vertices edges value)
end J
namespace T
export GeneralOddHigherResidueQuaternaryJoin
  (nativeTable zeroOne oneZero native_value value_pins halves_iff)
end T
namespace E
export Holant.LocalDrafts.TetrahedralCompletion.ExternalOddCompletion.Structure
  (twoConstants ordinary_terminal_decomposition)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (D : M.Minimal G) {k : ℕ} (ha : D.arity=k+2)

def terminal : Network AlgebraicComplex (k+2) :=
  reboundary (toNative D.graph) (finCongr ha)

theorem terminal_uses : Uses (terminal G D ha) (kCoordinates (original G)) :=
  toNative_uses (original G) _ D.uses

theorem terminal_native : Native (terminal G D ha) := toNative_native _ D.ordinary

private theorem reindex_constants {n m : ℕ} (h : n=m) (c d : AlgebraicComplex) :
    Tensor.reindex (finCongr h) (E.twoConstants (n:=n) c d)=E.twoConstants (n:=m) c d := by
  subst m
  rfl

theorem terminal_value (hk : 0<k) :
    (terminal G D ha).denote=E.twoConstants (M.endpoint G D false) (M.endpoint G D true) := by
  have hh : 3≤D.arity := by omega
  have hd := E.ordinary_terminal_decomposition D.graph.denote D.odd hh (M.noCuts G D)
  funext x
  rw [terminal,reboundary_denote,toNative_denote,hd]
  exact congrFun (reindex_constants ha (M.endpoint G D false) (M.endpoint G D true)) x

section Join
variable {F : SignatureFamily AlgebraicComplex}
variable (L R : Network AlgebraicComplex (k+2))
variable (hLF : Uses L F) (hRF : Uses R F) (hLX : Native L) (hRX : Native R)

include hLF hRF in
theorem join_uses : Uses (J.network L R (fun _ => Signature.disequality)) F := by
  intro v
  change (⟨_,(J.finite L R (fun _ => Signature.disequality)).vertex
    ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)⟩ :
      AnySignature AlgebraicComplex) ∈ F
  generalize (Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v = w
  cases w with
  | inl i => exact hLF i
  | inr i => exact hRF i

include hLX hRX in
theorem join_native : Native (J.network L R (fun _ => Signature.disequality)) := by
  intro e
  change (J.finite L R (fun _ => Signature.disequality)).edge
    ((Fintype.equivFin (J.Edges L R)).symm e)=Signature.disequality
  generalize (Fintype.equivFin (J.Edges L R)).symm e = w
  rcases w with (i | i) | i
  · exact hLX i
  · exact hRX i
  · rfl

def middleSwap : Equiv.Perm (Fin 4) := Equiv.swap 1 2

theorem reordered_deq (c : AlgebraicComplex) :
    Tensor.reindex middleSwap (T.nativeTable c)=c • ExactTwoSignatures.E := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex_apply,middleSwap,Equiv.swap_apply_def,T.nativeTable,T.zeroOne,T.oneZero,
      funext_iff,Fin.forall_fin_succ,Pi.smul_apply,smul_eq_mul,ExactTwoSignatures.E_reference,
      h0,h1,h2,h3]

theorem reordered_pin (c : AlgebraicComplex) :
    Signature.contract Signature.disequality
      (Tensor.reindex middleSwap (fun x : Fin 4 → Bool => if x=T.zeroOne then c else 0))=
      c • GeneralEOPinnedDescentNetwork.directed01 := by
  funext x
  rw [Signature.contract_disequality]
  have hcons (a b : Bool) : Fin.cons a (Fin.cons b x)=![a,b,x 0,x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hcons,hcons]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Tensor.reindex_apply,middleSwap,Equiv.swap_apply_def,
      T.zeroOne,funext_iff,Fin.forall_fin_succ,Pi.smul_apply,smul_eq_mul,
      GeneralEOPinnedDescentNetwork.directed01,h0,h1]

def deqGraph := reboundary (J.network L L (fun _ => Signature.disequality)) middleSwap

theorem deq_value (hk : 0<k) (c d : AlgebraicComplex) (hL : L.denote=E.twoConstants c d) :
    (deqGraph L).denote=(c*d) • ExactTwoSignatures.E := by
  funext x
  rw [deqGraph,reboundary_denote,J.denote,hL,E.twoConstants,T.native_value hk]
  exact congrFun (reordered_deq (c*d)) x

include hLF in
theorem deq_uses : Uses (deqGraph L) F := join_uses L L hLF hLF
include hLX in
theorem deq_native : Native (deqGraph L) := join_native L L hLX hLX

def pinGraph := (reboundary (J.network L R (fun _ => Signature.disequality)) middleSwap).contract
  Signature.disequality

theorem pure_join (c d : AlgebraicComplex) (hL : L.denote=purePin c false (k+2))
    (hR : R.denote=purePin d true (k+2)) :
    (J.network L R (fun _ => Signature.disequality)).denote=
      (fun x : Fin 4 → Bool => if x=T.zeroOne then c*d else 0) := by
  rw [J.denote,hL,hR,T.value_pins]
  funext x
  simp [T.halves_iff,T.zeroOne,Signature.disequality]

theorem pin_value (c d : AlgebraicComplex) (hL : L.denote=purePin c false (k+2))
    (hR : R.denote=purePin d true (k+2)) :
    (pinGraph L R).denote=(c*d) • GeneralEOPinnedDescentNetwork.directed01 := by
  rw [pinGraph,Network.denote_contract]
  have hv : (reboundary (J.network L R (fun _ => Signature.disequality)) middleSwap).denote=
      Tensor.reindex middleSwap (fun x : Fin 4 → Bool => if x=T.zeroOne then c*d else 0) := by
    funext x
    rw [reboundary_denote,pure_join L R c d hL hR]
    rfl
  rw [hv]
  exact reordered_pin (c*d)

include hLF hRF in
theorem pin_uses : Uses (pinGraph L R) F := join_uses L R hLF hRF
include hLX hRX in
theorem pin_native : Native (pinGraph L R) := by
  intro e
  refine Fin.cases rfl (fun e => ?_) e
  exact join_native L R hLX hRX e

theorem deq_counts :
    (deqGraph L).shape.vertices=2*L.shape.vertices ∧
    (deqGraph L).shape.edges=2*L.shape.edges+k := by
  change (J.network L L (fun _ => Signature.disequality)).shape.vertices=_ ∧
    (J.network L L (fun _ => Signature.disequality)).shape.edges=_
  rw [J.vertices,J.edges]
  constructor <;> omega

theorem pin_counts :
    (pinGraph L R).shape.vertices=L.shape.vertices+R.shape.vertices ∧
    (pinGraph L R).shape.edges=L.shape.edges+R.shape.edges+k+1 := by
  change (J.network L R (fun _ => Signature.disequality)).shape.vertices=_ ∧
    (J.network L R (fun _ => Signature.disequality)).shape.edges+1=_
  rw [J.vertices,J.edges]
  exact ⟨rfl,rfl⟩
end Join

/-- The two arms specify genuine native graphs, exact original chart labels,
and nonzero actual scalars. No normalization or oracle access is assumed. -/
def PinOrDEQ (F : SignatureFamily AlgebraicComplex) : Prop :=
  (∃ P : Network AlgebraicComplex 2,Uses P F ∧ Native P ∧
    ∃ c : AlgebraicComplex,c≠0 ∧ P.denote=c • GeneralEOPinnedDescentNetwork.directed01) ∨
  (∃ Q : Network AlgebraicComplex 4,Uses Q F ∧ Native Q ∧
    ∃ c : AlgebraicComplex,c≠0 ∧ Q.denote=c • ExactTwoSignatures.E)

theorem of_two_endpoints (hh : 3≤D.arity)
    (h0 : M.endpoint G D false≠0) (h1 : M.endpoint G D true≠0) :
    PinOrDEQ (kCoordinates (original G)) := by
  let k := D.arity-2
  have ha : D.arity=k+2 := by dsimp [k]; omega
  have hk : 0<k := by dsimp [k]; omega
  let L := terminal G D ha
  exact Or.inr ⟨deqGraph L,deq_uses L (terminal_uses G D ha),
    deq_native L (terminal_native G D ha),M.endpoint G D false*M.endpoint G D true,
    mul_ne_zero h0 h1,deq_value L hk _ _ (terminal_value G D ha hk)⟩

/-- Both support signs and d≥3 suffice for a structural directed pin or DEQ4
supplier, even if the original minimal terminal has one vanishing endpoint. -/
theorem producer (hh : 3≤D.arity)
    (hs : ¬CommonOneSided (kCoordinates (original G))) :
    PinOrDEQ (kCoordinates (original G)) := by
  obtain ⟨L,R,hL,hR,h0,h1⟩ :=
    GeneralOddHigherResidueQuaternaryEndpoints.both_endpoints G D hh hs
  have hLhigh : 3≤L.arity := by omega
  have hRhigh : 3≤R.arity := by omega
  by_cases hL1 : M.endpoint G L true≠0
  · exact of_two_endpoints G L hLhigh h0 hL1
  by_cases hR0 : M.endpoint G R false≠0
  · exact of_two_endpoints G R hRhigh hR0 h1
  have hL1z : M.endpoint G L true=0 := not_not.mp hL1
  have hR0z : M.endpoint G R false=0 := not_not.mp hR0
  let k := D.arity-2
  have ha : D.arity=k+2 := by dsimp [k]; omega
  have hk : 0<k := by dsimp [k]; omega
  let U := terminal G L (hL.trans ha)
  let V := terminal G R (hR.trans ha)
  have hU : U.denote=purePin (M.endpoint G L false) false (k+2) := by
    rw [show U.denote=E.twoConstants (M.endpoint G L false) (M.endpoint G L true)
      from terminal_value G L (hL.trans ha) hk,hL1z]
    funext x
    simp [E.twoConstants,purePin]
  have hV : V.denote=purePin (M.endpoint G R true) true (k+2) := by
    rw [show V.denote=E.twoConstants (M.endpoint G R false) (M.endpoint G R true)
      from terminal_value G R (hR.trans ha) hk,hR0z]
    funext x
    simp [E.twoConstants,purePin]
  exact Or.inl ⟨pinGraph U V,
    pin_uses U V (terminal_uses G L (hL.trans ha)) (terminal_uses G R (hR.trans ha)),
    pin_native U V (terminal_native G L (hL.trans ha)) (terminal_native G R (hR.trans ha)),
    M.endpoint G L false*M.endpoint G R true,mul_ne_zero h0 h1,pin_value U V _ _ hU hV⟩

/-- The fully source-facing structural alternative selects every actual
terminal internally from one original odd row and the two original charge
signs. Its nonprimitive lower bound is the original finite support gcd. -/
theorem source (j : Fin s) (hj : Odd (a j.val)) (hnz : G j≠0)
    (hs : ¬CommonOneSided (kCoordinates (original G)))
    (hd : 3≤GeneralOddResidueGcd.supportGcd G) :
    PinOrDEQ (kCoordinates (original G)) := by
  let D := GeneralOddMinimalTerminal.select G j hj hnz
  have he := GeneralOddResidueConservation.minimal_arity_eq_supportGcd G D hs
  exact producer G D (by omega) hs

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHigherResidueQuaternaryPinOrDEQ
