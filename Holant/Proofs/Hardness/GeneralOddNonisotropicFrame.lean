import Holant.Proofs.Hardness.GeneralOddUnarySource
import Holant.ReedMuller.CoefficientAtlas.ContractionTransport

/-! An unnormalised bilinear frame determined by an actual unary.  No square
root, projective rescaling, or new oracle coefficient is introduced.  Capping
with an actual copy of U is exactly restriction to false in this frame. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicFrame
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.GeneralExtraction
open NamedContraction NativeCopies SupportCaps
open GeneralOddUnaryOrdinary
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {n : ℕ}

def frame (u : Signature K 1) : Kernel K
  | false,false => u (fun _ => false)
  | false,true => u (fun _ => true)
  | true,false => -u (fun _ => true)
  | true,true => u (fun _ => false)

def norm (u : Signature K 1) : K :=
  u (fun _ => false)^2+u (fun _ => true)^2

def chart (u : Signature K 1) (f : Signature K n) : Signature K n :=
  Signature.coordinateAction (fun _ => frame u) f

def inverse (u : Signature K 1) : Kernel K :=
  fun b c => (norm u)⁻¹*frame u c b

theorem inverse_frame (u : Signature K 1) (hu : norm u≠0) :
    Kernel.mul (inverse u) (frame u)=Signature.equality := by
  funext b c
  cases b <;> cases c <;>
    simp [Kernel.mul,inverse,frame,Signature.equality]
  · calc
      _ = (norm u)⁻¹*norm u := by simp [norm]; ring
      _ = 1 := inv_mul_cancel₀ hu
  · ring
  · ring
  · calc
      _ = (norm u)⁻¹*norm u := by simp [norm]; ring
      _ = 1 := inv_mul_cancel₀ hu

theorem frame_inverse (u : Signature K 1) (hu : norm u≠0) :
    Kernel.mul (frame u) (inverse u)=Signature.equality := by
  funext b c
  cases b <;> cases c <;>
    simp [Kernel.mul,inverse,frame,Signature.equality]
  · calc
      _ = (norm u)⁻¹*norm u := by simp [norm]; ring
      _ = 1 := inv_mul_cancel₀ hu
  · ring
  · ring
  · calc
      _ = (norm u)⁻¹*norm u := by simp [norm]; ring
      _ = 1 := inv_mul_cancel₀ hu

theorem chart_injective (u : Signature K 1) (hu : norm u≠0) :
    Function.Injective (chart (n:=n) u) := by
  intro f g he
  have h := congrArg (Signature.coordinateAction (fun _ => inverse u)) he
  simpa only [chart,Signature.coordinateAction_cancel _ _ (fun _ => inverse_frame u hu)] using h

theorem chart_unary (u f : Signature K 1) (b : Bool) :
    chart u f (fun _ => b)=
      frame u b false*f (fun _ => false)+frame u b true*f (fun _ => true) := by
  unfold chart Signature.coordinateAction
  rw [←(Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  simp only [Fin.prod_univ_one,Fintype.sum_bool]
  exact add_comm _ _

theorem chart_self (u : Signature K 1) : chart u u=purePin (norm u) false 1 := by
  funext x
  have hx : x=(fun _ => x 0) := by funext i; exact congrArg x (Subsingleton.elim _ _)
  rw [hx,chart_unary]
  cases x 0 <;> simp [frame,purePin,norm,funext_iff,pow_two]
  all_goals ring

/-- One literal Eq edge joins U to the old first boundary port of N. -/
def capHead (U : Network K 1) (N : Network K (n+1)) : Network K n :=
  (reboundary (U.tensor N) (finCongr (by omega : 1+(n+1)=n+2))).contract Signature.equality

private theorem cap_left (a b : Bool) (x : Fin n → Bool) :
    (fun i : Fin 1 => (Fin.cons a (Fin.cons b x) : Fin (n+2) → Bool)
      ((finCongr (by omega : 1+(n+1)=n+2)) (Fin.castAdd (n+1) i)))=(fun _ => a) := by
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  rfl

private theorem cap_right (a b : Bool) (x : Fin n → Bool) :
    (fun i : Fin (n+1) => (Fin.cons a (Fin.cons b x) : Fin (n+2) → Bool)
      ((finCongr (by omega : 1+(n+1)=n+2)) (Fin.natAdd 1 i)))=Fin.cons b x := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  have he : (finCongr (by omega : 1+(n+1)=n+2)) (Fin.natAdd 1 j.succ)=j.succ.succ := by
    apply Fin.ext
    simp
  rw [he]
  rfl

theorem capHead_denote (U : Network K 1) (N : Network K (n+1)) (x : Fin n → Bool) :
    (capHead U N).denote x=
      U.denote (fun _ => false)*N.denote (Fin.cons false x)+
      U.denote (fun _ => true)*N.denote (Fin.cons true x) := by
  rw [capHead,Network.denote_contract]
  simp only [Signature.contract,reboundary_denote,Network.denote_tensor,
    Signature.tensor_apply,cap_left,cap_right]
  simp [Signature.equality,add_comm]

/-- The coefficients of every cap remain in the old field.  In particular no
factor q, q inverse, or square root is silently dropped here. -/
theorem chart_capHead (U : Network K 1) (N : Network K (n+1)) (x : Fin n → Bool) :
    chart U.denote (capHead U N).denote x=chart U.denote N.denote (Fin.cons false x) := by
  simp only [chart]
  rw [ReedMuller.CoefficientAtlas.coordinateAction_head]
  simp only [Fintype.sum_bool,frame,Signature.coordinateAction,Signature.pin,capHead_denote,
    Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem capHead_uses (F : SignatureFamily K) (U : Network K 1) (N : Network K (n+1))
    (hU : Uses U F) (hN : Uses N F) : Uses (capHead U N) F :=
  tensor_uses F U N hU hN

def Ordinary (N : Network K n) : Prop := ∀ e,N.edge e=Signature.equality

theorem tensor_ordinary {m : ℕ} (U : Network K n) (N : Network K m)
    (hU : Ordinary U) (hN : Ordinary N) : Ordinary (U.tensor N) := by
  intro e
  change (Network.tensorFinite U N).edge
    ((Fintype.equivFin (Fin U.shape.edges ⊕ Fin N.shape.edges)).symm e)=_
  cases (Fintype.equivFin (Fin U.shape.edges ⊕ Fin N.shape.edges)).symm e with
  | inl e => exact hU e
  | inr e => exact hN e

theorem capHead_ordinary (U : Network K 1) (N : Network K (n+1))
    (hU : Ordinary U) (hN : Ordinary N) : Ordinary (capHead U N) := by
  intro e
  refine Fin.cases rfl (fun e => ?_) e
  exact tensor_ordinary U N hU hN e

theorem capHead_vertices (U : Network K 1) (N : Network K (n+1)) :
    (capHead U N).shape.vertices=U.shape.vertices+N.shape.vertices :=
  Network.tensor_vertices U N

theorem capHead_edges (U : Network K 1) (N : Network K (n+1)) :
    (capHead U N).shape.edges=U.shape.edges+1+N.shape.edges := by
  change (U.tensor N).shape.edges+1=_
  rw [Network.tensor_edges]
  omega

theorem chart_reboundary (u : Signature K 1) (N : Network K n) (e : Equiv.Perm (Fin n))
    (x : Fin n → Bool) :
    chart u (reboundary N e).denote x=chart u N.denote (fun i => x (e i)) := by
  have he : (reboundary N e).denote=Tensor.reindex e N.denote := by
    funext y
    exact reboundary_denote N e y
  rw [he,chart,ReedMuller.CoefficientAtlas.coordinateAction_reindex]
  rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicFrame
