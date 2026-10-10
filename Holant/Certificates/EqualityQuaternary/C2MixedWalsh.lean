import Holant.Certificates.EqualityQuaternary.C2MixedNetwork
import Holant.Certificates.EqualityQuaternary.C2OneCopy
import Holant.EightVertex.ProductAnchor.TemplateTransport

/-! Exact Walsh transport of the actual two-copy gadget. The two internal
physical equality paths become two kernels 2I, producing the recorded 4.
The displayed block order is 13|24,14|23,12|34 at the new boundary.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.C2.Mixed
open Holant Holant.Marked Holant.Tractable
open Holant.Projective.CyclicQuaternary
open Holant.Projective.CyclicQuaternary.Physical hiding Scalar Mat
open Holant.ReedMuller.CoefficientAtlas
set_option backward.isDefEq.respectTransparency false

def gatherOrder : Fin 3 → Fin 8 → Fin 8 :=
  ![![0,4,1,5,2,3,6,7],![0,4,2,6,1,3,5,7],![0,4,3,7,1,2,5,6]]
def gatherInverse : Fin 3 → Fin 8 → Fin 8 :=
  ![![0,2,4,5,1,3,6,7],![0,4,2,5,1,6,3,7],![0,4,5,2,1,6,7,3]]
def gather (p : Fin 3) : Equiv.Perm (Fin 8) where
  toFun := gatherOrder p
  invFun := gatherInverse p
  left_inv := by
    have h : ∀ p i,gatherInverse p (gatherOrder p i)=i := by decide
    exact h p
  right_inv := by
    have h : ∀ p i,gatherOrder p (gatherInverse p i)=i := by decide
    exact h p

def template (E : Mat) (q : Signature Scalar 4) (p : Fin 3) : Signature Scalar 4 :=
  Signature.contract E (Signature.contract E (Tensor.reindex (gather p).symm (Signature.tensor q q)))

theorem template_left (p : Fin 3) (a b : Bool) (w : Word) :
    (fun i : Fin 4 => (Fin.cons a (Fin.cons a (Fin.cons b (Fin.cons b w))) : Fin 8 → Bool)
      ((gather p).symm (Fin.castAdd 4 i))) = join p false a b (w 0) (w 1) := by
  funext i; fin_cases p <;> fin_cases i <;> rfl
theorem template_right (p : Fin 3) (a b : Bool) (w : Word) :
    (fun i : Fin 4 => (Fin.cons a (Fin.cons a (Fin.cons b (Fin.cons b w))) : Fin 8 → Bool)
      ((gather p).symm (Fin.natAdd 4 i))) = join p false a b (w 2) (w 3) := by
  funext i; fin_cases p <;> fin_cases i <;> rfl

theorem output_eq_template (q : Signature Scalar 4) (p : Fin 3) :
    output q p=template Signature.equality q p := by
  funext w
  simp only [template,Signature.contract_equality,Tensor.reindex_apply,
    Signature.tensor_apply,template_left,template_right,output,Fintype.sum_bool]
  ac_rfl

theorem template_action (M E : Mat) (q : Signature Scalar 4) (p : Fin 3) :
    template E (Signature.coordinateAction (fun _ => M) q) p =
      Signature.coordinateAction (fun _ => M) (template (Kernel.pullback E M) q p) := by
  unfold template
  rw [←EightVertex.ProductAnchor.coordinateAction_tensor,
    ←coordinateAction_reindex,coordinateAction_contract,coordinateAction_contract]

theorem contract_kernel_scale {n : ℕ} (c : Scalar) (E : Mat) (f : Signature Scalar (n+2)) :
    Signature.contract (c • E) f=c • Signature.contract E f := by
  funext w
  simp [Signature.contract,Finset.mul_sum,mul_assoc]
  ring

theorem contract_value_scale {n : ℕ} (c : Scalar) (E : Mat) (f : Signature Scalar (n+2)) :
    Signature.contract E (c • f)=c • Signature.contract E f := by
  funext w
  simp [Signature.contract,Finset.mul_sum]
  ring

theorem template_kernel_scale (c : Scalar) (E : Mat) (q : Signature Scalar 4) (p : Fin 3) :
    template (c • E) q p=c^2 • template E q p := by
  simp only [template,contract_kernel_scale,contract_value_scale,smul_smul,pow_two]

theorem physical_equality_walsh : Kernel.pullback (Signature.equality : Mat) P = (2 : Scalar) • Signature.equality := by
  funext a b
  cases a <;> cases b <;> norm_num [Kernel.pullback,Kernel.mul_apply,Kernel.transpose,P,Signature.equality]

/-- The actual original q is retained on the left. All normalization is analytic. -/
theorem output_walsh (q : Signature Scalar 4) (p : Fin 3) :
    walsh (output q p)=(4 : Scalar) • output (walsh q) p := by
  have hback : Signature.coordinateAction (fun _ => P) (walsh q)=q :=
    Signature.coordinateAction_cancel _ _ (fun _ => P_Pinv) q
  have he : output q p = Signature.coordinateAction (fun _ => P) ((4 : Scalar) • output (walsh q) p) := by
    conv_lhs => rw [←hback]
    rw [output_eq_template,template_action,physical_equality_walsh,template_kernel_scale]
    norm_num [←output_eq_template]
  rw [he]
  exact Signature.coordinateAction_cancel _ _ (fun _ => Pinv_P) _

def mixedTable (x y z : Scalar) : Signature Scalar 4 :=
  ofCoordinates 0 0 ![(x,x),(y,y),(z,-z)]

def row (p : Fin 3) (x y z : Scalar) : Signature Scalar 4 :=
  if p=0 then ofCoordinates (x^2) (x^2) ![(0,0),(y^2+z^2,y^2+z^2),(0,0)]
  else if p=1 then ofCoordinates (y^2) (y^2) ![(0,0),(x^2+z^2,x^2+z^2),(0,0)]
  else ofCoordinates (z^2) (z^2) ![(0,0),(x^2+y^2,x^2+y^2),(2*x*y,2*x*y)]

theorem mixed_table_output (p : Fin 3) (x y z : Scalar) :
    output (mixedTable x y z) p=row p x y z := by
  funext w
  fin_cases p <;> cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp [output,mixedTable,row,ofCoordinates,join,h0,h1,h2,h3] <;> ring

/-- All three rows are the exact Walsh coefficients of actual gadget outputs. -/
theorem physical_mixed_table (q : Signature Scalar 4) (x y z : Scalar)
    (h : walsh q=mixedTable x y z) (p : Fin 3) :
    walsh (output q p)=(4 : Scalar) • row p x y z := by
  rw [output_walsh,h,mixed_table_output]

end Holant.Certificates.EqualityQuaternary.C2.Mixed
