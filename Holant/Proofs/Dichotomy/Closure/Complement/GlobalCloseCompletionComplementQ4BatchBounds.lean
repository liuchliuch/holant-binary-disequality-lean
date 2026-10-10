import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Batch
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4NodeBounds
import Holant.Proofs.BinaryInterpolation.OracleAnswerBounds

/-! The arithmetic budgets of the actual query transcript and root list are
computed from the original graph bytes. The coefficient family contains only
six fixed literals and the complete original native-X dictionary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4BatchBounds
open Holant Holant.Algebraic Holant.Complexity Holant.OneHot
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution
open Holant.LocalDrafts.BinaryInterpolation
namespace B
export GlobalCloseCompletionComplementQ4Batch
  (Input inputEncoding queryEncoding oldTables count roots target sampleCount queries preprocessing
   pre answered initial resultState result queriesComputes)
end B
namespace M
export GlobalCloseCompletionComplementQ4NodeBounds (roots_length roots_bound power)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {degree s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin s)→Signature K (a i.val))
variable (N : NativeAntiTargetSource.Output H 4) (v : Fin 4→K) (support : Bool) (j : Fin 4)
abbrev Index:=Fin 6 ⊕ ExactSignatureTables.CoefficientIndex s 1 a
def coordinates : Index (s:=s) (a:=a)→Fin degree→ℚ
  | .inl i=>F.decode.symm (![v 0,v 1,v 2,v 3,-1,1] i)
  | .inr i=>(B.oldTables F H).coefficient i
abbrev coeff:=fun i=>F.decode (coordinates F H v i)
theorem unit : coeff F H v (.inl 5)=1:=by simp [coeff,coordinates]
theorem neg : coeff F H v (.inl 4)= -1:=by simp [coeff,coordinates]
theorem rate (i : Fin 4) : ArithmeticSize.Bound (coeff F H v) 1 (v i) := by
  have h:=ArithmeticSize.Bound.coefficient (coeff:=coeff F H v) (.inl (Fin.castAdd 2 i))
  fin_cases i <;> simpa [coeff,coordinates] using h

theorem answer (q : ExactSignatureTables.Input s 1 a) :
    ArithmeticSize.Bound (coeff F H v) ((q.val.vertices.length+q.val.edges.length)+q.val.edges.length)
      ((B.oldTables F H).evaluate F q) := by
  apply OracleAnswerBounds.network_bound _ (.inl 5) (unit F H v)
    (q.val.realize q.property (fun i x=>F.decode ((B.oldTables F H).vertex i x))
      (fun i x y=>F.decode ((B.oldTables F H).edge i x y)))
    (fun z x=>.inr (.inl ⟨q.val.signatureLabel q.property z,x⟩))
    (fun z x y=>.inr (.inr (q.val.edgeLabel q.property z,x,y)))
    (fun _ _=>rfl) (fun _ _ _=>rfl) Fin.elim0

def answerPolynomial : Polynomial ℕ:=2*(B.queriesComputes F H N v support j).outputBound.bound

theorem emitted_answer (x : B.Input H N) (q : ExactSignatureTables.Input s 1 a)
    (member : q∈B.queries H N v support j x) :
    ArithmeticSize.Bound (coeff F H v)
      ((answerPolynomial F H N v support j).eval ((B.inputEncoding H N).encode x).length)
      ((B.oldTables F H).evaluate F q) := by
  have hmember:=OracleBatch.member_length_le
    ((B.queries H N v support j x).map (B.queryEncoding (s:=s) (a:=a)).encode)
    ((B.queryEncoding (s:=s) (a:=a)).encode q) (List.mem_map.mpr ⟨q,member,rfl⟩)
  have hlist:=(B.queriesComputes F H N v support j).outputBound.length_le x
  rw [OracleBatch.list_encode] at hlist
  have hsize:=q.val.counts_le_encoded_length
  apply (answer F H v q).mono (.inl 5) (unit F H v)
  change q.val.vertices.length+q.val.edges.length≤((B.queryEncoding (s:=s) (a:=a)).encode q).length at hsize
  simp only [answerPolynomial,Polynomial.eval_mul,Polynomial.eval_ofNat]
  omega

def degreePolynomial : Polynomial ℕ:=(Polynomial.X+1)^4
def listPolynomial : Polynomial ℕ:=degreePolynomial+1
def rootPolynomial : Polynomial ℕ:=4*Polynomial.X+1
def valuePolynomial : Polynomial ℕ:=answerPolynomial F H N v support j+1
def scalarPolynomial : Polynomial ℕ:=Polynomial.X+1

theorem count_bound (x : B.Input H N) : B.count H N x≤((B.inputEncoding H N).encode x).length:=
  occurrences_le_input_length s x.val

theorem root_length (x : B.Input H N) :
    (B.roots H N v support j x).length=(B.count H N x+1)^4:=M.roots_length v support j _

theorem roots_budget (x : B.Input H N) :
    ∀z∈B.roots H N v support j x,ArithmeticSize.Bound (coeff F H v)
      (rootPolynomial.eval ((B.inputEncoding H N).encode x).length) z := by
  intro z hz
  have h:=M.roots_bound (coeff F H v) (.inl 5) (unit F H v) v (rate F H v) support j (B.count H N x) z hz
  apply h.mono (.inl 5) (unit F H v)
  have bound:=count_bound H N x
  simp only [rootPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  omega

theorem target_budget (x : B.Input H N) :
    ArithmeticSize.Bound (coeff F H v)
      (scalarPolynomial.eval ((B.inputEncoding H N).encode x).length) (B.target H N v support j x) := by
  cases support
  · exact (M.power (coeff F H v) (rate F H v j) (B.count H N x)).mono (.inl 5) (unit F H v)
      (by have h:=count_bound H N x; simpa [scalarPolynomial] using Nat.le_add_right_of_le h)
  · exact ArithmeticSize.Bound.zero (.inl 5) _

theorem initial_values (x : B.Input H N) :
    ∀z∈(B.initial F H N v support j x).2.1,ArithmeticSize.Bound (coeff F H v)
      ((valuePolynomial F H N v support j).eval ((B.inputEncoding H N).encode x).length) z := by
  intro z hz
  change z∈(if support then 0::(B.queries H N v support j x).map ((B.oldTables F H).evaluate F)
    else (B.queries H N v support j x).map ((B.oldTables F H).evaluate F)) at hz
  have ha (z : K) (hz : z∈(B.queries H N v support j x).map ((B.oldTables F H).evaluate F)) :
      ArithmeticSize.Bound (coeff F H v)
        ((valuePolynomial F H N v support j).eval ((B.inputEncoding H N).encode x).length) z := by
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hz
    exact (emitted_answer F H N v support j x q hq).mono (.inl 5) (unit F H v) (by simp [valuePolynomial])
  cases support <;> simp only [Bool.false_eq_true,ite_false,ite_true,List.mem_cons] at hz
  · exact ha z hz
  · rcases hz with rfl|hz
    · exact ArithmeticSize.Bound.zero (.inl 5) _
    · exact ha z hz

theorem initial_length (x : B.Input H N) :
    (B.initial F H N v support j x).2.1.length=(B.count H N x+1)^4+1 := by
  change (if support then 0::(B.queries H N v support j x).map ((B.oldTables F H).evaluate F)
    else (B.queries H N v support j x).map ((B.oldTables F H).evaluate F)).length=_
  cases support <;> simp [B.queries,B.sampleCount,root_length]

theorem initial_denominator (x : B.Input H N) :
    ArithmeticSize.Bound (coeff F H v)
      (scalarPolynomial.eval ((B.inputEncoding H N).encode x).length) (B.initial F H N v support j x).2.2.2 := by
  change ArithmeticSize.Bound _ _ (if support then 1 else B.target H N v support j x)
  cases support
  · exact target_budget F H N v false j x
  · exact ArithmeticSize.Bound.one.mono (.inl 5) (unit F H v) (Nat.zero_le _)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4BatchBounds
end
