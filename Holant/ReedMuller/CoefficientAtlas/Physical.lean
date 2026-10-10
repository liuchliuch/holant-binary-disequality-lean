import Holant.ReedMuller.CoefficientAtlas.Fourier
import Holant.ReedMuller.CoefficientAtlas.ContractionTransport

namespace Holant.ReedMuller.CoefficientAtlas
open Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

def walshInverse (a b : Bool) : ℂ := walshKernel a b / 2

def walsh {n : ℕ} (f : Signature ℂ n) : Signature ℂ n :=
  Signature.coordinateAction (fun _ => walshInverse) f

theorem walsh_mul_inverse : Kernel.mul walshKernel walshInverse=Signature.equality := by
  funext a b
  cases a <;> cases b <;> norm_num [Kernel.mul,walshInverse,walshKernel,Signature.equality]

theorem inverse_mul_walsh : Kernel.mul walshInverse walshKernel=Signature.equality := by
  funext a b
  cases a <;> cases b <;> norm_num [Kernel.mul,walshInverse,walshKernel,Signature.equality]

theorem physical_of_walsh {n : ℕ} (f : Signature ℂ n) :
    Signature.coordinateAction (fun _ => walshKernel) (walsh f)=f :=
  Signature.coordinateAction_cancel _ _ (fun _ => walsh_mul_inverse) f

theorem walsh_of_physical {n : ℕ} (q : Signature ℂ n) :
    walsh (Signature.coordinateAction (fun _ => walshKernel) q)=q :=
  Signature.coordinateAction_cancel _ _ (fun _ => inverse_mul_walsh) q

/-- Original ordered physical I/X closure; the edge is the actual literal
kernel, before any Walsh bookkeeping. -/
def physicalCard (f : Signature ℂ 8) (p : Fin 28) (minus : Bool) : Signature ℂ 6 :=
  Signature.contract (if minus then Signature.disequality else Signature.equality)
    (Tensor.reindex (ports p).symm f)

theorem fill_eq_cons (p : Fin 28) (b : Bool) (y : Fin 6 → Bool) :
    fill p b y=fun i => (Fin.cons b (Fin.cons b y) : Fin 8 → Bool) ((ports p).symm i) := by
  funext i
  simp only [fill]
  generalize (ports p).symm i = j
  fin_cases j <;> rfl

theorem plusCard_eq_contract (q : Signature ℂ 8) (p : Fin 28) :
    plusCard q p=fun y => 2*Signature.contract Signature.equality (Tensor.reindex (ports p).symm q) y := by
  funext y
  rw [Signature.contract_equality]
  simp only [plusCard,fill_eq_cons,Tensor.reindex]

theorem walsh_pullback_equality : Kernel.pullback (Signature.equality : Kernel ℂ) walshKernel=
    fun a b => 2*Signature.equality a b := by
  funext a b
  cases a <;> cases b <;> norm_num [Kernel.pullback,Kernel.mul,Kernel.transpose,walshKernel,Signature.equality]

theorem contract_scale_kernel {n : ℕ} (c : ℂ) (E : Kernel ℂ) (q : Signature ℂ (n+2)) :
    Signature.contract (fun a b => c*E a b) q=fun y => c*Signature.contract E q y := by
  funext y
  simp [Signature.contract,Finset.mul_sum,mul_assoc,mul_add]

/-- Exact Eq. rm-card-pencil plus row: original physical I-card in Walsh
coordinates equals 2*(a_T+a_Tij), with the actual original port permutation. -/
theorem walsh_physical_plus (f : Signature ℂ 8) (p : Fin 28) :
    walsh (physicalCard f p false)=plusCard (walsh f) p := by
  have H : physicalCard f p false=
      Signature.coordinateAction (fun _ => walshKernel) (plusCard (walsh f) p) := by
    unfold physicalCard
    simp only [Bool.false_eq_true,ite_false]
    conv_lhs => rw [←physical_of_walsh f]
    rw [←coordinateAction_reindex,coordinateAction_contract,walsh_pullback_equality,
      contract_scale_kernel,plusCard_eq_contract]
  rw [H,walsh_of_physical]

/-- Complete normalized one-step physical I/X deck; zero cards are retained. -/
def PhysicalDeck (f : Signature ℂ 8) : Prop :=
  ∀ p : Fin 28, ∀ minus : Bool,
    walsh (physicalCard f p minus)=0 ∨
      ∃ M : WeightedMatching, M.value=walsh (physicalCard f p minus)

theorem plusCards_of_physical (f : Signature ℂ 8) (h : PhysicalDeck f) :
    ∀ p : Fin 28, plusCard (walsh f) p=0 ∨
      ∃ M : WeightedMatching, M.value=plusCard (walsh f) p := by
  intro p
  simpa only [walsh_physical_plus] using h p false

end
end Holant.ReedMuller.CoefficientAtlas
