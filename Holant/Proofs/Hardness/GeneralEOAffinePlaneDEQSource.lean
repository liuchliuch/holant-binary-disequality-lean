import Holant.Proofs.Hardness.GeneralEOAffinePlaneDEQ
import Holant.Complexity.FixedGadgetSubstitution.ScaledAdjoin

/-! A same-field fixed-gadget programme removes the adjoined literal DEQ4
row. Its compiled graph replaces every marked occurrence by24 original
vertices and46 native edges; its compiled correction multiplies the original
oracle answer by the inverse scalar to the actual occurrence count. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneDEQSource
open Holant Holant.Complexity Holant.Algebraic Computability FixedGadgetSubstitution
namespace C
export GeneralEOAffinePlaneChain (Mat table)
end C
namespace L
export GeneralEOAffinePlaneChainLabels (literal kernels template_actual)
end L
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s 1 a)

def G (i : Fin s) : Signature K (a i.val) := fun x => F.decode (T.vertex i x)
variable (j : Fin s) (M : Signature K 4)
variable (hM : (⟨a j.val,G F T j⟩ : AnySignature K)=⟨4,M⟩)
variable (e : Equiv.Perm (Fin 4))
abbrev labels := L.literal (G F T) j M hM e 23
abbrev g := (labels F T j M hM e).template
abbrev hg := (labels F T j M hM e).wellFormed
abbrev A := sourceArity (Adjoin.templates s a (g F T j M hM e))
variable (c : K)
abbrev coordinates := ScaledAdjoin.coordinates F T (g F T j M hM e) (hg F T j M hM e) c
abbrev tables := sourceTables (Adjoin.templates s a (g F T j M hM e)) T
  (coordinates F T j M hM e c)
abbrev signatures := G F (tables F T j M hM e c)
abbrev Input := ExactSignatureTables.Input (s+1) 1 (A F T j M hM e)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+1) 1 (A F T j M hM e)
abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev sourceValue := (tables F T j M hM e c).evaluate F

variable (hn : ∀i b b',F.decode (T.edge i b b')=Signature.disequality b b')
variable (f : Signature K 2) (hplane : Tensor.reindex e M=EOBinaryPlaneCore.lift f)
variable (hp : C.table f^24=c • (1 : C.Mat (K:=K)))

include hn hplane hp in
theorem macro_scaled :
    ((g F T j M hM e).network (hg F T j M hM e) (G F T)
      (fun i b b' => F.decode (T.edge i b b'))).denote=c • ExactTwoSignatures.E := by
  have hk : (fun i b b' => F.decode (T.edge i b b'))=L.kernels (K:=K) := by
    funext i b b'
    exact hn i b b'
  rw [hk,L.template_actual]
  exact GeneralEOAffinePlaneDEQ.power_denote M e f hplane 23 c hp

private def decodeAny (z : AnySignature (Fin d→ℚ)) : AnySignature K :=
  ⟨z.1,fun x => F.decode (z.2 x)⟩

/-- Every old row keeps its original signature and label. -/
theorem old_signature (i : Fin s) :
    (⟨A F T j M hM e i.val,
      signatures F T j M hM e c ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩⟩ : AnySignature K)=
      ⟨a i.val,G F T i⟩ := by
  have he : (⟨A F T j M hM e i.val,
      coordinates F T j M hM e c ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩⟩ :
        AnySignature (Fin d→ℚ))=⟨a i.val,T.vertex i⟩ :=
    Sigma.ext (Adjoin.old_boundary (g F T j M hM e) i)
      (ScaledAdjoin.old_coordinates F T (g F T j M hM e) (hg F T j M hM e) c i)
  exact congrArg (decodeAny F) he

include hn hplane hp in
/-- The appended row is literally E in the original coefficient field. -/
theorem new_signature (hc : c≠0) :
    (⟨A F T j M hM e s,
      signatures F T j M hM e c ⟨s,Nat.lt_succ_self s⟩⟩ : AnySignature K)=
      ⟨4,ExactTwoSignatures.E⟩ := by
  have he : (⟨A F T j M hM e s,
      coordinates F T j M hM e c ⟨s,Nat.lt_succ_self s⟩⟩ : AnySignature (Fin d→ℚ))=
      ⟨4,fun x => F.decode.symm (((g F T j M hM e).network (hg F T j M hM e)
        (G F T) (fun i b b' => F.decode (T.edge i b b'))).denote x/c)⟩ :=
    Sigma.ext (Adjoin.new_boundary (g F T j M hM e))
      (ScaledAdjoin.new_coordinates F T (g F T j M hM e) (hg F T j M hM e) c)
  have h := congrArg (decodeAny F) he
  refine h.trans ?_
  change (⟨4,fun x => F.decode (F.decode.symm
    (((g F T j M hM e).network (hg F T j M hM e) (G F T)
      (fun i b b' => F.decode (T.edge i b b'))).denote x/c))⟩ : AnySignature K)=_
  congr 1
  funext x
  rw [LinearEquiv.apply_symm_apply,macro_scaled F T j M hM e c hn f hplane hp]
  exact mul_div_cancel_left₀ (ExactTwoSignatures.E x) hc

include hn in
theorem native_tables : ∀i b b',F.decode ((tables F T j M hM e c).edge i b b')=
    Signature.disequality b b' := hn

/-- Actual template replacement, occurrence counter and scalar-power decoder.
Both input and output retain exactly F.encoding; no field identification is
used or assumed. -/
def reduction (hc : c≠0) : PolyTimeOracleReduction
    (inputEncoding F T j M hM e) F.encoding (targetEncoding (s:=s) (a:=a)) F.encoding
    (sourceValue F T j M hM e c) (T.evaluate F) :=
  ScaledAdjoin.reduction F T (g F T j M hM e) (hg F T j M hM e) c hc

@[simp] theorem macro_vertices : (g F T j M hM e).vertices.length=24 :=
  GeneralEOAffinePlaneChainLabels.template_vertices (G F T) j M hM e 23

@[simp] theorem macro_edges : (g F T j M hM e).edges.length=46 :=
  GeneralEOAffinePlaneChainLabels.template_edges (G F T) j M hM e 23

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneDEQSource
