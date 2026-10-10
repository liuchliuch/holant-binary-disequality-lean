import Holant.ReedMuller.WeightTwoIntegration.ExceptionalTopology

/-! Inverse analytic Walsh reconstruction, with both parity cosets and the
equality-anchor identities. No basis matrix is installed as a physical vertex. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open scoped BigOperators
open CoefficientAtlas ExceptionalTopology
set_option backward.isDefEq.respectTransparency false

def even4 : Signature ℂ 4 := fun x =>
  if (((x 0).xor (x 1)).xor (x 2)).xor (x 3) then 0 else 1

def flipFirst (x : Fin 4 → Bool) : Fin 4 → Bool := ![!(x 0),x 1,x 2,x 3]

def endpoint (s : ℂ) : Signature ℂ 4 := fun y =>
  (if y = fun _ => false then 1 else 0) + (if y = fun _ => true then s else 0)

theorem paired_Q_endpoint (d : ExceptionalData) :
    pairedOutput d.Q = fun y => d.coefficient * endpoint d.sigma y := by
  funext y
  cases h0 : y 0 <;> cases h1 : y 1 <;> cases h2 : y 2 <;> cases h3 : y 3 <;>
    simp [pairedOutput,d.Q_exact,endpoint,funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]

theorem coordinateAction_scalar {n : ℕ} (M : Fin n → Kernel ℂ)
    (c : ℂ) (q : Signature ℂ n) :
    Signature.coordinateAction M (fun y => c * q y) =
      fun x => c * Signature.coordinateAction M q x := by
  funext x
  simp only [Signature.coordinateAction,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem endpoint_reconstruction (s : ℂ) (x : Fin 4 → Bool) :
    Signature.coordinateAction (fun _ => walshKernel) (endpoint s) x =
      1 + s * (if (((x 0).xor (x 1)).xor (x 2)).xor (x 3) then -1 else 1) := by
  simp only [Signature.coordinateAction,endpoint,mul_add,Finset.sum_add_distrib,mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Fin.prod_univ_succ,walshKernel,h0,h1,h2,h3]

theorem exceptional_reconstruction (d : ExceptionalData) (x : Fin 4 → Bool) :
    Signature.coordinateAction (fun _ => walshKernel) (pairedOutput d.Q) x =
      d.coefficient *
        (1 + d.sigma * (if (((x 0).xor (x 1)).xor (x 2)).xor (x 3) then -1 else 1)) := by
  rw [paired_Q_endpoint,coordinateAction_scalar]
  exact congrArg (d.coefficient * ·) (endpoint_reconstruction d.sigma x)

theorem exceptional_reconstruction_even (d : ExceptionalData) (hs : d.sigma = 1) :
    Signature.coordinateAction (fun _ => walshKernel) (pairedOutput d.Q) =
      fun x => (2 * d.coefficient) * even4 x := by
  funext x
  rw [exceptional_reconstruction,hs]
  unfold even4
  split <;> ring

theorem exceptional_reconstruction_odd (d : ExceptionalData) (hs : d.sigma = -1) :
    Signature.coordinateAction (fun _ => walshKernel) (pairedOutput d.Q) =
      fun x => (2 * d.coefficient) * even4 (flipFirst x) := by
  funext x
  rw [exceptional_reconstruction,hs]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [even4,flipFirst,h0,h1,h2,h3] <;> ring

theorem flipFirst_twice (x : Fin 4 → Bool) : flipFirst (flipFirst x) = x := by
  funext i
  fin_cases i <;> simp [flipFirst]

/-- Source matrix U = D P⁻¹, with D = diag(1,i). -/
def anchorU : Kernel ℂ := fun a b => (if a then Complex.I else 1) * walshKernel a b / 2

/-- Source inverse U⁻¹ = P D⁻¹. -/
def anchorUInverse : Kernel ℂ := fun a b => walshKernel a b * (if b then -Complex.I else 1)

def eq4 : Signature ℂ 4 := fun x => if ∀ i, x i = x 0 then 1 else 0

theorem anchorU_inverse : Kernel.mul anchorU anchorUInverse = Signature.equality ∧
    Kernel.mul anchorUInverse anchorU = Signature.equality := by
  constructor <;> funext a b <;> cases a <;> cases b <;>
    norm_num [anchorU,anchorUInverse,walshKernel,Kernel.mul_apply,Signature.equality,
      Complex.I_sq] <;> ring_nf <;> norm_num [Complex.I_sq]

/-- Exact, unnormalized equality-anchor transformation. -/
theorem anchor_even4 : Signature.coordinateAction (fun _ => anchorU) even4 =
    fun x => (1/2 : ℂ) * eq4 x := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    norm_num [Signature.coordinateAction,sum_words4,Fin.prod_univ_succ,
      anchorU,walshKernel,even4,eq4,Fin.forall_fin_succ,h0,h1,h2,h3,Complex.I_sq] <;> ring

theorem anchor_native_kernel : Kernel.pullback Signature.disequality anchorUInverse =
    fun a b => (2 : ℂ) * Signature.equality a b := by
  funext a b
  cases a <;> cases b <;>
    norm_num [Kernel.pullback,Kernel.mul_apply,Kernel.transpose,anchorUInverse,
      walshKernel,Signature.disequality,Signature.equality,Complex.I_sq]

end Holant.ReedMuller.WeightTwoIntegration
