import Holant.Proofs.Hardness.EqualModulusThreeModeChain
import Holant.Proofs.Hardness.RealDenseSignTwistStageAccess

/-! All-occurrence exact replacement by a fixed positive n-copy original-q
chain. Its polynomial constants may depend on n, which the closed source
fixes to the torsion exponent of the original field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EqualModulusThreeModeStageAccess
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity TargetInput targetEncoding)
end Q
namespace V
export RealDenseSignTwistStageAccess (value signatures kernels tables evaluate)
end V
namespace N
export EqualModulusThreeModeChain (first second third template valid template_denote counts)
export ThreeModeSignatures (original)
end N
namespace Cap
export Holant.LocalDrafts.Hardness.ControlledCap (controlledSubstitution)
end Cap
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (a b c : K) (n : ℕ) (hn : 0<n)
local instance : CharZero K := algebraRat.charZero K

def normalized : Signature K 4 :=
  N.original (N.first a b n) (N.second a b n) (N.third c n)

def templates (_i : ℕ) : Template := N.template n

theorem valid : ∀i<1,(templates n i).WellFormed 1 1 Q.arity := fun _ _=>N.valid n

theorem arity_exact : sourceArity (templates n)=Q.arity := rfl

def coordinates (_i : Fin 1) (x : Fin (sourceArity (templates n) _i.val)→Bool) : Fin d→ℚ :=
  F.decode.symm (normalized a b c n x)

include hn in
theorem template_denote (i : Fin 1) :
    ((templates n i.val).network (valid n i.val i.isLt)
      (fun j x=>F.decode ((V.tables F (N.original a b c)).vertex j x))
      (fun j x y=>F.decode ((V.tables F (N.original a b c)).edge j x y))).denote=
      (if i.val=0 then (1 : K) else 1) • (fun x=>F.decode (coordinates F a b c n i x)) := by
  fin_cases i
  simp only [V.tables,coordinates,LinearEquiv.apply_symm_apply]
  change ((N.template n).network (N.valid n)
    (fun _ : Fin 1=>N.original a b c) (fun _ : Fin 1=>Signature.disequality)).denote=
      (1 : K) • normalized a b c n
  rw [one_smul]
  exact N.template_denote a b c n hn

abbrev generatedValue :=
  (sourceTables (templates n) (V.tables F (N.original a b c)) (coordinates F a b c n)).evaluate F

theorem source_value (r : Q.TargetInput) :
    generatedValue F a b c n r=V.value (normalized a b c n) r := by
  simp only [generatedValue,ExactSignatureTables.evaluate_eq_decoded,sourceTables,
    coordinates,V.tables,LinearEquiv.apply_symm_apply]
  rfl

def query : Q.TargetInput→Q.TargetInput :=
  Compiler.value 1 1 Q.arity (templates n) 1 Q.arity
    (compilerHypotheses (templates n) (valid n))

def queryComputes : Computes Q.targetEncoding Q.targetEncoding (query n) :=
  Compiler.computes 1 1 Q.arity (templates n) 1 Q.arity
    (compilerHypotheses (templates n) (valid n))

include hn in
theorem query_counts (r : Q.TargetInput) :
    (query n r).val.vertices.length=n*r.val.vertices.length ∧
    (query n r).val.edges.length=r.val.edges.length+2*(n-1)*r.val.vertices.length := by
  have hv (row : RawVertex) : (templates n row.1).vertices.length=n := (N.counts n hn).1
  have he (row : RawVertex) : (templates n row.1).edges.length=2*(n-1) := (N.counts n hn).2
  change (replace (templates n) r.val).vertices.length=_ ∧
    (replace (templates n) r.val).edges.length=_
  rw [replace_vertex_count,replace_edge_count]
  simp only [hv,he]
  simp [List.sum_replicate,Nat.mul_comm]

include hn in
theorem query_value (r : Q.TargetInput) :
    V.value (N.original a b c) (query n r)=V.value (normalized a b c n) r := by
  have hp := replacement_scale_power (templates n) r.val r.property (valid n)
    (V.signatures (normalized a b c n)) (V.signatures (N.original a b c)) V.kernels 0 (1 : K) (fun i=>by
      fin_cases i
      change ((N.template n).network (N.valid n)
        (fun _ : Fin 1=>N.original a b c) (fun _ : Fin 1=>Signature.disequality)).denote=
          (1 : K) • normalized a b c n
      simpa [normalized] using N.template_denote a b c n hn)
  have hv : V.value (N.original a b c) (query n r)=
      (1 : K)^occurrences 0 r.val*V.value (normalized a b c n) r := hp
  simpa only [one_pow,one_mul] using hv

def substitution :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (generatedValue F a b c n) ((V.tables F (N.original a b c)).evaluate F) :=
  Cap.controlledSubstitution F (templates n) (valid n)
    (V.tables F (N.original a b c)) (coordinates F a b c n)
    0 (1 : K) (by simp) (template_denote F a b c n hn)

attribute [local irreducible] substitution

def source :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (V.value (normalized a b c n)) (V.value (N.original a b c)) := by
  have r := substitution F a b c n hn
  have hs : generatedValue F a b c n=V.value (normalized a b c n) := funext (source_value F a b c n)
  have ht : (V.tables F (N.original a b c)).evaluate F=V.value (N.original a b c) :=
    funext (V.evaluate F (N.original a b c))
  rw [hs,ht] at r
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EqualModulusThreeModeStageAccess
