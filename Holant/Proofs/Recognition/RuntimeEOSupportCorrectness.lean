import Holant.Proofs.Recognition.RuntimeEOSupportCheck

/-! Exact domain and two-sign meaning of the runtime support scans. The
intermediate support-table law is proved by the original-root/view frontend
when composed; no such law is a supplied final criterion or evaluator. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOSupportCorrectness
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open RuntimeEOSupportCheck
open ComplexIsolation.RootSearchDriver (cross mem_cross)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {n : ℕ} (zero : (Fin n → Bool) → Bool)
def source : Table := (SparseTransform.allWords n).map (fun x => (List.ofFn x,zero x))
def sourceRow (x : Fin n → Bool) : RuntimeEOViewSupport.ZeroRow := (List.ofFn x,zero x)
def sourceTriple (a b c : Fin n → Bool) : Triple := (sourceRow zero a,sourceRow zero b,sourceRow zero c)

theorem row_mem (x : Fin n → Bool) : sourceRow zero x∈source zero :=
  List.mem_map.mpr ⟨x,SparseTransform.mem_allWords x,rfl⟩

theorem row_of_mem (r : RuntimeEOViewSupport.ZeroRow) (hr : r∈source zero) :
    ∃x,r=sourceRow zero x := by
  obtain ⟨x,_,hx⟩ := List.mem_map.mp hr
  exact ⟨x,hx.symm⟩

theorem xor_source (a b c : Fin n → Bool) :
    xorWord (List.ofFn a,List.ofFn b,List.ofFn c)=List.ofFn (tripleXor a b c) := by
  unfold xorWord
  rw [List.length_ofFn,RuntimeTensorRowsSoundness.map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [PositiveCertificateMachine.getD_ofFn,tripleXor]

theorem lookup_source (x : Fin n → Bool) : lookupZero (source zero,List.ofFn x)=zero x := by
  apply Bool.eq_iff_iff.mpr
  simp only [lookupZero,source,List.any_map,List.any_eq_true,Function.comp_def,Bool.and_eq_true,
    decide_eq_true_eq,SparseTransform.mem_allWords,true_and]
  constructor
  · rintro ⟨y,he,hz⟩
    have hy : y=x := List.ofFn_injective he
    simpa only [hy] using hz
  · intro h
    exact ⟨x,rfl,h⟩

theorem triple_mem (a b c : Fin n → Bool) : sourceTriple zero a b c∈triples (source zero) :=
  mem_cross.mpr ⟨row_mem zero a,mem_cross.mpr ⟨row_mem zero b,row_mem zero c⟩⟩

theorem triple_of_mem (r : Triple) (hr : r∈triples (source zero)) :
    ∃a b c,r=sourceTriple zero a b c := by
  obtain ⟨ha,hbc⟩ := mem_cross.mp hr
  obtain ⟨hb,hc⟩ := mem_cross.mp hbc
  obtain ⟨a,ha⟩ := row_of_mem zero r.1 ha
  obtain ⟨b,hb⟩ := row_of_mem zero r.2.1 hb
  obtain ⟨c,hc⟩ := row_of_mem zero r.2.2 hc
  exact ⟨a,b,c,by rw [show r=(r.1,r.2.1,r.2.2) from rfl,ha,hb,hc]; rfl⟩

variable (f : Signature AlgebraicComplex n) (hz : ∀x,zero x=true ↔ f x=0)

include hz in
theorem nonzero_flag (x : Fin n → Bool) : zero x=false ↔ f x≠0 := by
  cases h : zero x <;> simpa only [h,Bool.false_eq_true,Bool.true_eq_false,not_false_eq_true,
    not_true_eq_false,false_iff,true_iff] using not_congr (hz x)

include hz in
theorem domain_bad (x : Fin n → Bool) : domainBad (sourceRow zero x)=true ↔
    f x≠0 ∧ 2*Holant.weight x≠n := by
  simp only [domainBad,sourceRow,RuntimeSupportFlags.wordWeight_source,List.length_ofFn,
    Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,nonzero_flag zero f hz,decide_eq_false_iff_not]

include hz in
theorem domain_empty : domainFailures (source zero)=[] ↔ Signature.CentralSupport f := by
  constructor
  · intro h x hx
    by_contra hfx
    have hm : sourceRow zero x∈domainFailures (source zero) :=
      List.mem_filter.mpr ⟨row_mem zero x,(domain_bad zero f hz x).mpr ⟨hfx,hx⟩⟩
    rw [h] at hm
    exact List.not_mem_nil hm
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro r hr
    obtain ⟨hm,hb⟩ := List.mem_filter.mp hr
    obtain ⟨x,rfl⟩ := row_of_mem zero r hm
    obtain ⟨hne,hweight⟩ := (domain_bad zero f hz x).mp hb
    exact hne (h x hweight)

include hz in
/-- Central support forces even arity whenever the signature is nonzero;
therefore an odd-arity domain failure is always witnessed by an actual word. -/
theorem domain_eo (hne : f≠0) : domainFailures (source zero)=[] ↔ IsEO (⟨n,f⟩ : AnySignature AlgebraicComplex) := by
  rw [domain_empty zero f hz]
  constructor
  · intro h
    have hex : ∃x,f x≠0 := by
      by_contra hn
      push_neg at hn
      exact hne (funext hn)
    obtain ⟨x,hx⟩ := hex
    have hn : n=2*Holant.weight x := by
      by_contra he
      exact hx (h x (Ne.symm he))
    exact ⟨⟨Holant.weight x,hn⟩,h⟩
  · exact And.right

def signOf (negative : Bool) : EOSign := if negative then .positive else .negative

theorem sign_failure (negative : Bool) (x : Fin n → Bool) :
    RuntimeSupportFlags.sign negative (List.ofFn x)=true ↔ (signOf negative).value*Holant.charge x≤0 := by
  rw [RuntimeSupportFlags.sign_correct]
  cases negative <;> simp only [signOf,UniformKSupport.signHolds,Bool.false_eq_true,ite_false,ite_true,
    EOSign.value,one_mul,neg_one_mul] <;> omega

include hz in
theorem triple_bad (negative : Bool) (a b c : Fin n → Bool) :
    tripleBad negative (source zero) (sourceTriple zero a b c)=true ↔
      f a≠0 ∧ f b≠0 ∧ f c≠0 ∧ f (tripleXor a b c)=0 ∧
        (signOf negative).value*Holant.charge (tripleXor a b c)≤0 := by
  simp only [tripleBad,sourceTriple,sourceRow,wordsOf,xor_source,lookup_source,Bool.and_eq_true,
    Bool.not_eq_true_eq_eq_false,nonzero_flag zero f hz,hz,sign_failure,and_assoc]

include hz in
theorem triples_empty (negative : Bool) : tripleFailures negative (source zero)=[] ↔
    ∀a b c,f a≠0 → f b≠0 → f c≠0 →
      f (tripleXor a b c)≠0 ∨ 0<(signOf negative).value*Holant.charge (tripleXor a b c) := by
  constructor
  · intro h a b c ha hb hc
    by_cases hd : f (tripleXor a b c)≠0
    · exact Or.inl hd
    · right
      by_contra hsgn
      have hm : sourceTriple zero a b c∈tripleFailures negative (source zero) :=
        List.mem_filter.mpr ⟨triple_mem zero a b c,
          (triple_bad zero f hz negative a b c).mpr ⟨ha,hb,hc,not_ne_iff.mp hd,not_lt.mp hsgn⟩⟩
      rw [h] at hm
      exact List.not_mem_nil hm
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro r hr
    obtain ⟨hm,hbad⟩ := List.mem_filter.mp hr
    obtain ⟨a,b,c,rfl⟩ := triple_of_mem zero r hm
    obtain ⟨ha,hb,hc,hd,hsgn⟩ := (triple_bad zero f hz negative a b c).mp hbad
    rcases h a b c ha hb hc with hne | hlt
    · exact hne hd
    · exact (not_lt_of_ge hsgn) hlt

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOSupportCorrectness
