import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ChainCompilerValidated
import Holant.Proofs.Dichotomy.Native.NativeAntiTargetSource
import Holant.Complexity.FixedGadgetSubstitution.Partition

/-! Exact native-X sample semantics of the emitted original-dictionary query.
The four spectral powers use the positive physical chain length k+1. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerSemantics
open Holant Holant.Complexity FixedGadgetSubstitution RawClosedNetwork
open Holant.LocalDrafts.BinaryInterpolation
namespace V
export GlobalCloseCompletionComplementQ4ChainCompilerValidated
  (macroArity SourceInput sourceEncoding Input inputEncoding intermediate query queryComputes chain_hypotheses)
end V
namespace O
export GlobalCloseCompletionComplementQ4ChainCompilerOccurrence (templates raw_eq_replace)
end O
namespace C
export GlobalCloseCompletionComplementQ4ChainCompilerNetwork (template_value valid)
end C
namespace R
export GlobalCloseCompletionComplementQ4ChainCompilerRecords (compile_eq)
end R
namespace S
export GlobalCloseCompletionComplementQ4Series (ofSpectrum)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

/-- An arity transport changes neither the row nor its ordered coefficient data. -/
theorem replacement_unscaled {K : Type} [Field K] {r s b : ℕ} {a A : ℕ→ℕ}
    (ts : ℕ→Template) (hg : ∀i<r,(ts i).WellFormed s b a)
    (ha : sourceArity ts=A) (q : RawClosedNetwork) (hq : q.WellFormed r b A)
    (source : (i : Fin r)→Signature K (A i.val))
    (H : (i : Fin s)→Signature K (a i.val)) (E : Fin b→Kernel K)
    (forms : ∀i : Fin r,(⟨(ts i.val).boundary,((ts i.val).network (hg i.val i.isLt) H E).denote⟩ : AnySignature K)=
      ⟨A i.val,source i⟩) :
    ((replace ts q).realize (replace_wellFormed ts q hq (fun i hi=>⟨hg i hi,congrFun ha i⟩)) H E).denote Fin.elim0=
      (q.realize hq source E).denote Fin.elim0 := by
  subst A
  have h:=replacement_partition ts q hq hg source H E (fun _=>1) (fun i=>by
    simp only [one_smul]
    exact eq_of_heq (Sigma.mk.inj_iff.mp (forms i)).2)
  simpa using h

variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (N : NativeAntiTargetSource.Output H 4)
theorem boundary : N.template.boundary=4:=rfl
abbrev arity:=V.macroArity (s:=s) a N.template
abbrev Source:=V.SourceInput (s:=s) (b:=1) a N.template
abbrev sourceEncoding:=V.sourceEncoding (s:=s) (b:=1) a N.template
abbrev Input:=Source H N × ℕ
abbrev inputEncoding:=V.inputEncoding (s:=s) (b:=1) a N.template
abbrev query:=V.query a N.template N.labels.wellFormed (boundary H N) (0 : Fin 1)
abbrev queryComputes:=V.queryComputes a N.template N.labels.wellFormed (boundary H N) (0 : Fin 1)
abbrev actual:=OriginalTables.tables N.template N.labels.wellFormed H (fun _ : Fin 1=>Signature.disequality)

def slot (f : Signature K 4) (i : Fin (s+1)) : Signature K (arity H N i.val):=
  if hi : i.val=s then
    OriginalTables.castSignature ((congrArg (arity H N) hi).trans (Adjoin.new_boundary N.template)).symm f
  else actual H N i

theorem slot_new (f : Signature K 4) :
    (⟨arity H N s,slot H N f ⟨s,Nat.lt_succ_self _⟩⟩ : AnySignature K)=⟨4,f⟩ := by
  simp only [slot,dif_pos rfl]
  exact OriginalTables.castSignature_any _ _

theorem slot_old (f : Signature K 4) (i : Fin s) :
    (⟨arity H N i.val,slot H N f ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩⟩ : AnySignature K)=⟨a i.val,H i⟩ := by
  simp only [slot,dif_neg (Nat.ne_of_lt i.isLt)]
  exact OriginalTables.tables_old _ _ _ _ i

theorem actual_new : (⟨arity H N s,actual H N ⟨s,Nat.lt_succ_self _⟩⟩ : AnySignature K)=
    ⟨4,N.network.denote⟩ := by
  refine (OriginalTables.tables_new _ _ _ _).trans ?_
  rw [NativeAntiTargetSource.template_exact]
  rfl


theorem chain_arity (k : ℕ) :
    sourceArity (O.templates (arity H N) s s 0 k)=arity H N := by
  funext i
  by_cases hi : i=s
  · subst i
    simp only [sourceArity,GlobalCloseCompletionComplementQ4ChainCompilerOccurrence.templates,if_pos rfl]
    exact (Adjoin.new_boundary N.template).symm
  · simp [sourceArity,O.templates,hi,identityTemplate]

theorem chain_forms (v : Fin 4→K) (form : N.network.denote=S.ofSpectrum v) (k : ℕ)
    (i : Fin (s+1)) :
    (⟨(O.templates (arity H N) s s 0 k i.val).boundary,
      ((O.templates (arity H N) s s 0 k i.val).network
        (V.chain_hypotheses a N.template (boundary H N) (0 : Fin 1) k i.val i.isLt).1
        (actual H N) (fun _ : Fin 1=>Signature.disequality)).denote⟩ : AnySignature K)=
      ⟨arity H N i.val,slot H N (S.ofSpectrum (fun j=>v j^(k+1))) i⟩ := by
  by_cases hi : i.val=s
  · have ie : i=(⟨s,Nat.lt_succ_self s⟩ : Fin (s+1)):=Fin.ext hi
    subst i
    refine Eq.trans ?_ (slot_new H N _).symm
    have h := C.template_value (arity H N) (⟨s,Nat.lt_succ_self _⟩ : Fin (s+1))
      (Adjoin.new_boundary N.template) (0 : Fin 1) v k (actual H N)
      (fun _ : Fin 1=>Signature.disequality) ((actual_new H N).trans (by rw [form])) rfl
    have ht := PhysicalQueries.templateSignature_eq _ _
      (V.chain_hypotheses a N.template (boundary H N) (0 : Fin 1) k s (Nat.lt_succ_self s)).1
      (C.valid (arity H N) (⟨s,Nat.lt_succ_self _⟩ : Fin (s+1)) (Adjoin.new_boundary N.template) (0 : Fin 1) k)
      (by simpa [GlobalCloseCompletionComplementQ4ChainCompilerOccurrence.templates] using (R.compile_eq s 0 k).symm) (actual H N) (fun _ : Fin 1=>Signature.disequality)
    exact ht.trans (by rw [h];rfl)
  · have ht := PhysicalQueries.templateSignature_eq _ (identityTemplate (arity H N) i.val)
      (V.chain_hypotheses a N.template (boundary H N) (0 : Fin 1) k i.val i.isLt).1
      (identityTemplate_wellFormed (b:=1) (arity H N) i)
      (by simp [GlobalCloseCompletionComplementQ4ChainCompilerOccurrence.templates,hi])
      (actual H N) (fun _ : Fin 1=>Signature.disequality)
    refine ht.trans ?_
    rw [identityTemplate_denote (arity H N) i (actual H N) (fun _ : Fin 1=>Signature.disequality)]
    change (⟨arity H N i.val,actual H N i⟩ : AnySignature K)=⟨arity H N i.val,slot H N _ i⟩
    congr 1
    symm
    unfold slot
    rw [dif_neg hi]

/-- The fixed expansion uses each literal original row and the actual macro. -/
theorem fixed_partition (x : Input H N) :
    ((query H N x).val.realize (query H N x).property H (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0=
      ((V.intermediate a N.template (boundary H N) (0 : Fin 1) x).val.realize
        (V.intermediate a N.template (boundary H N) (0 : Fin 1) x).property (actual H N)
          (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0 := by
  exact replacement_unscaled (Adjoin.templates s a N.template) (Adjoin.wellFormed N.template N.labels.wellFormed)
    rfl _ _ (actual H N) H (fun _ : Fin 1=>Signature.disequality) (fun _=>rfl)

/-- Exact positive sample: every marked source vertex is replaced by k+1 copies
of the actual quaternary network; every old row and every X edge is preserved. -/
theorem sample (v : Fin 4→K) (form : N.network.denote=S.ofSpectrum v) (x : Input H N) :
    ((query H N x).val.realize (query H N x).property H (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0=
      (x.1.val.realize x.1.property (slot H N (S.ofSpectrum (fun i=>v i^(x.2+1))))
        (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0 := by
  rw [fixed_partition]
  have h:=replacement_unscaled (O.templates (arity H N) s s 0 x.2)
    (fun i hi=>(V.chain_hypotheses a N.template (boundary H N) (0 : Fin 1) x.2 i hi).1)
    (chain_arity H N x.2) x.1.val x.1.property
    (slot H N (S.ofSpectrum (fun i=>v i^(x.2+1)))) (actual H N)
    (fun _ : Fin 1=>Signature.disequality) (chain_forms H N v form x.2)
  have he:=O.raw_eq_replace (s+1) 1 (arity H N) s s 0 (x.2,x.1)
  exact (Holant.Complexity.BinaryInterpolation.Chains.Compiler.Validated.raw_denote_congr _ _
    (V.intermediate a N.template (boundary H N) (0 : Fin 1) x).property _ he
    (actual H N) (fun _ : Fin 1=>Signature.disequality)).trans h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerSemantics
end
