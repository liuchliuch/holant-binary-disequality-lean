import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZCapGraph

/-! A symmetric GHZ row and the two actual pins produce either an already
weighted equality or a nonsingular semisimple cap. The defective case uses
five real unary walks, not an assumed arbitrary-unary interpolation oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZCapSelection
open Holant Holant.Tractable Holant.Complexity
open Holant.Certificates.MatchingContractionClosure
open Holant.Complexity.BinaryInterpolation
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization OrdinaryNegativeCubicGadgets
namespace C
export GlobalCloseCompletionSymmetricGHZCapGraph
  (symmetric pencil pencil_det pencil_trace cap cap_form walk cap_jordan)
end C
namespace R
export GlobalCloseCompletionSymmetricGHZRegularCap (hyperdet five_cap_parameters)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

def discriminant (B : Binary (K:=K)) : K := (Matrix.trace B)^2-4*Matrix.det B
def Semisimple (B : Binary (K:=K)) : Prop := discriminant B≠0 ∨ ∃c : K,c≠0 ∧ B=c • (1 : Binary (K:=K))

theorem scalar_of_defective_diagonal (B : Binary (K:=K))
    (symmetric : B false true=B true false) (off : B false true=0)
    (det : Matrix.det B≠0) (disc : discriminant B=0) :
    ∃c : K,c≠0 ∧ B=c • (1 : Binary (K:=K)) := by
  have other : B true false=0:=symmetric.symm.trans off
  have sq : (B false false-B true true)^2=0 := by
    simp [discriminant,Matrix.trace,det_entries,off,other] at disc
    linear_combination disc
  have equal : B false false=B true true:=sub_eq_zero.mp (sq_eq_zero_iff.mp sq)
  have nonzero : B false false≠0 := by
    intro zero
    apply det
    rw [det_entries,zero,off,other]
    ring
  refine ⟨B false false,nonzero,?_⟩
  ext i j
  cases i <;> cases j <;> simp [Matrix.one_apply,off,other,equal]

theorem defective_roots (B : Binary (K:=K)) (det : Matrix.det B≠0) (disc : discriminant B=0) :
    Matrix.trace B/2≠0 ∧ Matrix.trace B=Matrix.trace B/2+Matrix.trace B/2 ∧
      Matrix.det B=(Matrix.trace B/2)*(Matrix.trace B/2) := by
  have two : (2:K)≠0:=by norm_num
  have form : Matrix.det B=(Matrix.trace B/2)*(Matrix.trace B/2) := by
    unfold discriminant at disc
    linear_combination (-1/4:K)*disc
  refine ⟨?_,by ring,form⟩
  intro zero
  exact det (by rw [form,zero,mul_zero])

variable {r : ℕ} {arity : ℕ→ℕ} {H : (i : Fin r)→Signature K (arity i.val)}
def matrix (N : Macro H 2) : Binary (K:=K) := binaryMatrix N.network.denote

theorem cap_matrix (N : Macro H 3) (U : Macro H 1) (a b c d : K)
    (form : N.network.denote=C.symmetric a b c d) :
    matrix (C.cap N U)=C.pencil a b c d (U.network.denote (fun _=>false)) (U.network.denote (fun _=>true)) := by
  funext i j
  change (C.cap N U).network.denote ![i,j]=_
  rw [C.cap_form N U a b c d _ _ form rfl rfl]
  rfl

theorem regularize (N : Macro H 3) (P U : Macro H 1) (a b c d : K)
    (form : N.network.denote=C.symmetric a b c d)
    (hyper : R.hyperdet a b c d≠0) (pin : P.network.denote=QuaternaryUnaryAccess.pin false)
    (nonzero : Matrix.det (matrix (C.cap N U))≠0) :
    ∃V : Macro H 1,Matrix.det (matrix (C.cap N V))≠0 ∧ Semisimple (matrix (C.cap N V)) := by
  classical
  let Q:=C.cap N U
  let B:=matrix Q
  have qb : Q.network.denote=binarySignature B:=(binarySignature_binaryMatrix _).symm
  by_cases disc : discriminant B=0
  swap
  · exact ⟨U,nonzero,Or.inl disc⟩
  by_cases off : B false true=0
  · refine ⟨U,nonzero,Or.inr (scalar_of_defective_diagonal B ?_ off nonzero disc)⟩
    dsimp only [B,Q]
    rw [cap_matrix N U a b c d form]
    rfl
  · let mu:=Matrix.trace B/2
    obtain ⟨mn,tr,dt⟩:=defective_roots B nonzero disc
    have wn : B false true/mu≠0:=div_ne_zero off mn
    obtain ⟨k,detK,discK⟩:=R.five_cap_parameters a b c d ((B false false-mu)/mu) (B false true/mu) hyper wn
    let D:=C.pencil a b c d (1+(k.val:K)*((B false false-mu)/mu)) ((k.val:K)*(B false true/mu))
    have detD : Matrix.det D≠0 := by simpa only [D,C.pencil_det] using detK
    have discD : discriminant D≠0 := by simpa only [discriminant,D,C.pencil_det,C.pencil_trace] using discK
    have physical : matrix (C.cap N (C.walk Q P k.val))=mu^k.val • D := by
      funext i j
      change (C.cap N (C.walk Q P k.val)).network.denote ![i,j]=_
      rw [C.cap_jordan N Q P a b c d form B qb pin mu mn tr dt k.val]
      rfl
    have scale : mu^k.val≠0:=pow_ne_zero _ mn
    refine ⟨C.walk Q P k.val,?_,Or.inl ?_⟩
    · rw [physical,Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ scale) detD
    · rw [physical]
      have same : discriminant (mu^k.val • D)=(mu^k.val)^2*discriminant D := by
        simp only [discriminant,Matrix.trace_smul,Matrix.det_smul,Fintype.card_bool,smul_eq_mul]
        ring
      rw [same]
      exact mul_ne_zero (pow_ne_zero _ scale) discD

theorem select (N : Macro H 3) (P : Bool→Macro H 1) (a b c d : K)
    (form : N.network.denote=C.symmetric a b c d) (hyper : R.hyperdet a b c d≠0)
    (pins : ∀v,(P v).network.denote=QuaternaryUnaryAccess.pin v) :
    (b=0 ∧ c=0 ∧ a≠0 ∧ d≠0) ∨
      ∃U : Macro H 1,Matrix.det (matrix (C.cap N U))≠0 ∧ Semisimple (matrix (C.cap N U)) := by
  classical
  have d0 : Matrix.det (matrix (C.cap N (P false)))=a*c-b^2 := by
    rw [cap_matrix N (P false) a b c d form,pins,C.pencil_det]
    simp [QuaternaryUnaryAccess.pin]
  have d1 : Matrix.det (matrix (C.cap N (P true)))=b*d-c^2 := by
    rw [cap_matrix N (P true) a b c d form,pins,C.pencil_det]
    simp [QuaternaryUnaryAccess.pin]
  by_cases h0 : a*c-b^2=0
  · by_cases h1 : b*d-c^2=0
    · left
      have middle : a*d-b*c≠0 := by intro zero;exact hyper (by simp [R.hyperdet,h0,h1,zero])
      have cz : c*(a*d-b*c)=0 := by linear_combination d*h0+b*h1
      have bz : b*(a*d-b*c)=0 := by linear_combination a*h1+c*h0
      have c0 : c=0:=(mul_eq_zero.mp cz).resolve_right middle
      have b0 : b=0:=(mul_eq_zero.mp bz).resolve_right middle
      refine ⟨b0,c0,?_,?_⟩
      · intro a0;exact middle (by simp [a0,b0,c0])
      · intro d0;exact middle (by simp [d0,b0,c0])
    · right
      exact regularize N (P false) (P true) a b c d form hyper (pins false) (by rwa [d1])
  · right
    exact regularize N (P false) (P false) a b c d form hyper (pins false) (by rwa [d0])


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZCapSelection
end
