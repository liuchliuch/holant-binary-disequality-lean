import Holant.Proofs.Hardness.GeneralEOAffinePlaneDEQProgramme
import Holant.Complexity.BinaryInterpolation.Chains.Compiler.OriginalCounts

/-! Exact physical replacement counts and coded-storage bounds of the same
DEQ-elimination programme. The replacement preserves all old edge IDs and
ports; each literal E occurrence adds23 vertices and46 native edges. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneDEQResources
open Holant Holant.Complexity Holant.Algebraic Computability FixedGadgetSubstitution
namespace D
export GeneralEOAffinePlaneDEQSource (G g hg A Input inputEncoding targetEncoding)
end D
namespace P
export GeneralEOAffinePlaneDEQProgramme (query templates sourceWithDEQ)
end P
namespace R
export Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
  (configurationWord codedStoragePolynomial coded_storage_le)
end R
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {d s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s 1 a)
variable (j : Fin s) (M : Signature K 4)
variable (hM : (⟨a j.val,D.G F T j⟩ : AnySignature K)=⟨4,M⟩)
variable (e : Equiv.Perm (Fin 4))

theorem query_counts (r : D.Input F T j M hM e) :
    (P.query F T j M hM e r).val.vertices.length=r.val.vertices.length+23*occurrences s r.val ∧
    (P.query F T j M hM e r).val.edges.length=r.val.edges.length+46*occurrences s r.val := by
  have hb : ∀v∈r.val.vertices,v.1<s+1 := by
    intro v hv
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hv
    exact (r.property.1 i).1
  constructor
  · have h := BinaryInterpolation.Chains.Compiler.OriginalFamily.macro_vertex_sum a
      (D.g F T j M hM e) r.val.vertices hb
    rw [←replace_vertex_count,GeneralEOAffinePlaneDEQSource.macro_vertices] at h
    change (replace (P.templates F T j M hM e) r.val).vertices.length=_
    change (replace (P.templates F T j M hM e) r.val).vertices.length+occurrences s r.val=
      r.val.vertices.length+24*occurrences s r.val at h
    omega
  · change (replace (P.templates F T j M hM e) r.val).edges.length=_
    rw [replace_edge_count,BinaryInterpolation.Chains.Compiler.OriginalFamily.macro_edge_sum a _ _ hb]
    rw [GeneralEOAffinePlaneDEQSource.macro_edges]
    rfl

variable (c : K) (hc : c≠0)
variable (hn : ∀i b b',F.decode (T.edge i b b')=Signature.disequality b b')
variable (f : Signature K 2) (hplane : Tensor.reindex e M=EOBinaryPlaneCore.lift f)
variable (hp : GeneralEOAffinePlaneChain.table f^24=c • (1 : GeneralEOAffinePlaneChain.Mat (K:=K)))

/-- A faithful serialized configuration, including every control state and
actual stack, is bounded for every certified execution prefix. -/
theorem coded_storage (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (D.targetEncoding (s:=s) (a:=a)) F.encoding (T.evaluate F) oracle)
    (r : GeneralEOSinglePinAmplificationCompiler.Input (s:=s+1) (a:=D.A F T j M hM e))
    (t : ℕ)
    (ht : t≤(P.sourceWithDEQ F T j M hM e c hc hn f hplane hp).reduction.time.eval
      ((GeneralEOSinglePinAmplificationProgramme.inputEncoding (s:=s+1) (a:=D.A F T j M hM e)).encode r).length)
    (z : (P.sourceWithDEQ F T j M hM e c hc hn f hplane hp).reduction.machine.Cfg)
    (hr : (P.sourceWithDEQ F T j M hM e c hc hn f hplane hp).reduction.machine.run oracle
      ((GeneralEOSinglePinAmplificationProgramme.inputEncoding (s:=s+1) (a:=D.A F T j M hM e)).encode r) t=some z) :
    (R.configurationWord (P.sourceWithDEQ F T j M hM e c hc hn f hplane hp).reduction.machine z).length≤
      (R.codedStoragePolynomial (P.sourceWithDEQ F T j M hM e c hc hn f hplane hp)).eval
        ((GeneralEOSinglePinAmplificationProgramme.inputEncoding (s:=s+1) (a:=D.A F T j M hM e)).encode r).length :=
  R.coded_storage_le (P.sourceWithDEQ F T j M hM e c hc hn f hplane hp) oracle ho r t ht z hr

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneDEQResources
