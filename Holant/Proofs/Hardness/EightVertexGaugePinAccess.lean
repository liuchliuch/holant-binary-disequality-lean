import Holant.Proofs.Hardness.EightVertexGaugePinLeaf
import Holant.Proofs.Dichotomy.Retained.StableDenseParityAlgebra
import Holant.Proofs.FiniteGroups.Stabilization.DirectScalars
import Holant.OpenNetworkComposition.Closure

/-! Exact continuation from a saved scaled computational pin. Retained I and
one native-X splice give the opposite pin with the SAME scalar. The original
pin then cuts the first port of any actual four-row, yielding its literal
scaled cubic slice. No normalization, free unary, or odd terminal is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePinAccess
open Holant Holant.Tractable Holant.OpenNetworkComposition
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
variable {K : Type} [Field K]

def scaledPin (b : Bool) (c : K) : Signature K 1 :=
  fun x => if x 0 = b then c else 0

theorem scaledPin_nonzero (b : Bool) (c : K) (hc : c ≠ 0) : scaledPin b c ≠ 0 := by
  intro zero
  have h := congrFun zero (fun _ => b)
  exact hc (by simpa [scaledPin] using h)

theorem flip_value (b : Bool) (c : K) :
    spliceTensor (scaledPin b c) OrdinaryNormalization.identitySignature 0 =
      scaledPin (!b) c := by
  funext x
  cases b <;> cases h : x 0 <;>
    simp [spliceTensor,scaledPin,OrdinaryNormalization.identitySignature,
      Signature.equality,Signature.disequality,Function.update,h]

theorem flip_actual (F : SignatureFamily K) (hI : RetainsIdentity F)
    (b : Bool) (c : K) (actual : Gadget.Realizes F .disequality (scaledPin b c)) :
    Gadget.Realizes F .disequality (scaledPin (!b) c) := by
  rw [← flip_value]
  exact realizes_splice F _ _ actual (Gadget.realizes_of_mem F .disequality _ hI) 0

/-- A single saved pin gives both computational bits, preserving its scalar. -/
theorem both_actual (F : SignatureFamily K) (hI : RetainsIdentity F)
    (b : Bool) (c : K) (actual : Gadget.Realizes F .disequality (scaledPin b c)) :
    ∀ d : Bool, Gadget.Realizes F .disequality (scaledPin d c) := by
  intro d
  have flip := flip_actual F hI b c actual
  cases b <;> cases d <;> first | exact actual | exact flip

theorem cross_pairing (b : Bool) (c : K) :
    Signature.connect Signature.disequality
      (fun a => scaledPin b c (fun _ => a))
      (fun a => scaledPin (!b) c (fun _ => a)) = c*c := by
  rw [Signature.connect_disequality]
  cases b <;> simp [scaledPin]

def sliceOrder : Equiv.Perm (Fin 5) where
  toFun := ![0,2,3,4,1]
  invFun := ![0,4,1,2,3]
  left_inv := by decide
  right_inv := by decide

def slice (q : Signature K 4) (u : Signature K 1) : Signature K 3 :=
  Signature.contract Signature.disequality (Tensor.reindex sliceOrder (Signature.tensor q u))

/-- The pin's bit is complemented by the native X edge, and original ports
1, 2, 3 remain in order. Its original scalar multiplies the literal slice. -/
theorem slice_value (q : Signature K 4) (b : Bool) (c : K) (x : Fin 3 → Bool) :
    slice q (scaledPin b c) x = c*q ![!b,x 0,x 1,x 2] := by
  rw [slice,Signature.contract_disequality]
  have left (a d : Bool) :
      (fun i : Fin 4 => (Fin.cons a (Fin.cons d x) : Fin 5 → Bool)
        (sliceOrder (Fin.castAdd 1 i))) = ![a,x 0,x 1,x 2] := by
    funext i
    fin_cases i <;> rfl
  have right (a d : Bool) :
      (fun i : Fin 1 => (Fin.cons a (Fin.cons d x) : Fin 5 → Bool)
        (sliceOrder (Fin.natAdd 4 i))) = fun _ => d := by
    funext i
    fin_cases i
    rfl
  simp only [Tensor.reindex_apply,Signature.tensor_apply,left,right]
  cases b <;> simp [scaledPin,mul_comm]

theorem slice_actual (F : SignatureFamily K) (hI : RetainsIdentity F)
    (q : Signature K 4) (u : Signature K 1)
    (hq : Gadget.Realizes F .disequality q) (hu : Gadget.Realizes F .disequality u) :
    Gadget.Realizes F .disequality (slice q u) := by
  have tensor := realizes_tensor F .disequality q u hq hu
  have ordered := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality _
    tensor sliceOrder.symm
  simp only [Equiv.symm_symm] at ordered
  exact realizes_contract_exact_of_identity F hI _ ordered

theorem dense_slice_nonzero (q : Signature K 4) (dense : StableDenseParityAlgebra.Dense q)
    (b : Bool) (c : K) (hc : c ≠ 0) : slice q (scaledPin b c) ≠ 0 := by
  intro zero
  have h := congrFun zero ![!b,false,false]
  rw [slice_value] at h
  have live : q ![!b,!b,false,false] ≠ 0 := by
    cases b
    · exact dense.2.2.2.2.2.2.1
    · exact dense.1
  exact mul_ne_zero hc live h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePinAccess
end
