import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNANDSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockBinarySource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingSource

/-! A traceless symmetric nonsingular binary and an isotropic full unary
produce an actual even weighted-NAND block unless the two fourth powers agree.
The counting source is unsigned and needs no literal X vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularNAND
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeMixedBlockData
namespace R
export OrdinaryNegativeMixedBlockRelabel (exactRecipe even_recipe coefficient_eq)
end R
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
end M
namespace B
export OrdinaryNegativeMixedBlockBinarySource (binary value controlled)
end B
namespace N
export OrdinaryNegativeNANDSource (source)
end N
namespace C
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue (coefficient)
end C
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K]

def traceless (x y : K) : Signature K 2 := fun z=>
  if z 0 then (if z 1 then -x else y) else (if z 1 then y else x)
def unary (u v : K) : Signature K 1 := fun z=>if z 0 then v else u

def arity (j : ℕ) : ℕ := if j=0 then 2 else 1

def table (x y u v : K) (j : Fin 2) : Signature K (arity j.val) :=
  match j with
  | ⟨0,_⟩=>traceless x y
  | ⟨1,_⟩=>unary u v
  | ⟨j+2,h⟩=>False.elim (by omega)

def recipe : Recipe (u:=1) (s:=2) (a:=fun _=>2+1) (b:=arity) :=
  fun _=>[⟨0,![.inr (0 : Fin 3),.inr (2 : Fin 3)]⟩,⟨0,![.inr (2 : Fin 3),.inr (1 : Fin 3)]⟩,
    ⟨0,![.inr (2 : Fin 3),.inl false]⟩,⟨0,![.inr (2 : Fin 3),.inl false]⟩,
    ⟨1,fun _=>.inr (0 : Fin 3)⟩,⟨1,fun _=>.inr (1 : Fin 3)⟩,
    ⟨1,fun _=>.inr (2 : Fin 3)⟩,⟨1,fun _=>.inr (2 : Fin 3)⟩]

theorem even_recipe : EvenRecipe recipe := by
  intro i q
  fin_cases i
  cases q with
  | inl b => cases b <;> decide
  | inr j => fin_cases j <;> decide

theorem coefficient_value (x y u v : K) (z : Fin 3→Bool) :
    coefficient (table x y u v) recipe 0 z=
      traceless x y ![z 0,z 2]*traceless x y ![z 2,z 1]*
        (traceless x y ![z 2,false])^2*
        (if z 0 then v else u)*(if z 1 then v else u)*(if z 2 then v else u)^2 := by
  change traceless x y ![z 0,z 2] * (traceless x y ![z 2,z 1] *
    (traceless x y ![z 2,false] * (traceless x y ![z 2,false] *
      ((if z 0 then v else u) * ((if z 1 then v else u) *
        ((if z 2 then v else u) * ((if z 2 then v else u)*1)))))))=_
  ring

def trace (x y u v : K) : Signature K 2 := M.trace (table x y u v) 1 recipe 0

theorem trace_formula (x y u v : K) (z : Fin 2→Bool) :
    trace x y u v z=(if z 0 then v else u)*(if z 1 then v else u)*
      (traceless x y ![z 0,false]*traceless x y ![false,z 1]*x^2*u^2+
       traceless x y ![z 0,true]*traceless x y ![true,z 1]*y^2*v^2) := by
  unfold trace M.trace
  simp_rw [coefficient_value]
  rw [←(Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  cases h0 : z 0 <;> cases h1 : z 1 <;>
    simp [traceless,Fin.addCases,h0,h1] <;> ring

variable (x y u v : K) (square : v^2= -u^2)

include square in
theorem trace_ff : trace x y u v ![false,false]=u^4*(x^4-y^4) := by
  rw [trace_formula]
  norm_num [traceless]
  rw [square]
  ring

include square in
theorem trace_ft : trace x y u v ![false,true]=u^3*v*x*y*(x^2+y^2) := by
  rw [trace_formula]
  norm_num [traceless]
  rw [square]
  ring

include square in
theorem trace_tf : trace x y u v ![true,false]=u^3*v*x*y*(x^2+y^2) := by
  rw [trace_formula]
  norm_num [traceless]
  rw [square]
  ring

include square in
theorem trace_tt : trace x y u v ![true,true]=0 := by
  rw [trace_formula]
  norm_num [traceless]
  rw [square]
  ring_nf
  simp

variable (nx : x≠0) (ny : y≠0) (nu : u≠0)
variable (det : x^2+y^2≠0) (fourth : x^4≠y^4)

include square nu in
theorem unary_second_nonzero : v≠0 := by
  intro zero
  have hz := square
  rw [zero,zero_pow (by decide),eq_neg_iff_add_eq_zero] at hz
  exact pow_ne_zero 2 nu (by simpa using hz)

variable {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (labels : Fin 2→Fin s)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=
  ⟨arity i.val,table x y u v i⟩)

def rows : Recipe (u:=1) (s:=s) (a:=fun _=>2+1) (b:=b) :=
  R.exactRecipe labels (table x y u v) H literal recipe

theorem rows_even : EvenRecipe (rows x y u v H labels literal) :=
  R.even_recipe labels (fun i=>congrArg Sigma.fst (literal i)) recipe even_recipe

theorem rows_trace (z : Fin 2→Bool) :
    M.trace H 1 (rows x y u v H labels literal) 0 z=trace x y u v z := by
  unfold trace rows
  simp only [M.trace,R.coefficient_eq]

variable [Algebra ℚ K] {d : ℕ} (F : FixedField K d) (e p0 p1 : Fin s)
variable (he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

/-- Literal weighted NAND, its unsigned counting programme, and the actual
even-block compiler. No disequality vertex is requested from the table. -/
def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 b) F.encoding count
      ((StableHigherCurrentEvenCSPSource.tables F H).evaluate F) := by
  let block := rows x y u v H labels literal
  have hf : B.binary H 1 block false false≠0 := by
    rw [B.binary,rows_trace,trace_ff x y u v square]
    exact mul_ne_zero (pow_ne_zero 4 nu) (sub_ne_zero.mpr fourth)
  have hv : v≠0 := unary_second_nonzero u v square nu
  have hft : B.binary H 1 block false true≠0 := by
    rw [B.binary,rows_trace,trace_ft x y u v square]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ nu) hv) nx) ny) det
  have htf : B.binary H 1 block true false≠0 := by
    rw [B.binary,rows_trace,trace_tf x y u v square]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ nu) hv) nx) ny) det
  have htt : B.binary H 1 block true true=0 := by
    rw [B.binary,rows_trace,trace_tt x y u v square]
  exact Programme.compose (N.source F (B.binary H 1 block) hf hft htf htt w)
    (B.controlled F H e p0 p1 he h0 h1 1 block (rows_even x y u v H labels literal))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularNAND
end
